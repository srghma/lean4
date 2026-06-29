// Lean compiler output
// Module: Lean.Elab.Deriving.Repr
// Imports: Lean.Meta.Inductive Lean.Elab.Deriving.Basic Lean.Elab.Deriving.Util
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_array_size, lean_array_to_list, lean_array_uget, lean_array_uget_borrowed,
    lean_array_uset, lean_infer_type, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_utf8_byte_size,
    lean_string_utf8_next_fast, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt,
    lean_usize_of_nat,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Iterate::l_String_Slice_positions;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_mkNumLit, l_Lean_Syntax_mkStrLit, l_Lean_mkSepArray, lean_mk_syntax_ident,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_append, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node5,
    l_Lean_Syntax_node6, l_Lean_Syntax_node7, l_Lean_addMacroScope, l_Lean_mkAtom,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_String_toRawSubstring_x27, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Core_mkFreshUserName,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Declaration::l_Lean_instInhabitedInductiveVal_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_elabCommand, l_Lean_Elab_Command_liftTermElabM___redArg,
};
use crate::r#gen::Lean::Elab::Deriving::Basic::{
    initialize_Lean_Elab_Deriving_Basic, l_Lean_Elab_registerDerivingHandler,
    runtime_initialize_Lean_Elab_Deriving_Basic,
};
use crate::r#gen::Lean::Elab::Deriving::Util::{
    initialize_Lean_Elab_Deriving_Util, l_Lean_Elab_Deriving_mkContext,
    l_Lean_Elab_Deriving_mkDiscrs, l_Lean_Elab_Deriving_mkHeader,
    l_Lean_Elab_Deriving_mkInstanceCmds, l_Lean_Elab_Deriving_mkLet,
    l_Lean_Elab_Deriving_mkLocalInstanceLetDecls,
    l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg,
    runtime_initialize_Lean_Elab_Deriving_Util,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed,
    l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Environment::{
    l_Lean_AsyncConstantInfo_toConstantInfo, l_Lean_Environment_findAsync_x3f,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_BinderInfo_isExplicit, l_Lean_Expr_fvarId_x21, l_Lean_Expr_isAppOf,
    l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList,
    l_Lean_MessageData_ofSyntax, l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l_Lean_FVarId_getBinderInfo___redArg, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed,
};
use crate::r#gen::Lean::Meta::Inductive::{
    initialize_Lean_Meta_Inductive, runtime_initialize_Lean_Meta_Inductive,
};
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_isProof, l_Lean_Meta_isType};
use crate::r#gen::Lean::MonadEnv::l_Lean_isInductiveCore;
use crate::r#gen::Lean::Structure::{l_Lean_getStructureFields, l_Lean_isStructure};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value:
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
    m_data: [82, 101, 112, 114, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15923304685029768128 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value:
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
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value:
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
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value:
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
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__5_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        101, 120, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__5_value)
            as *mut crate::leanh::LeanObject,
        17201320286889277233 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7_value:
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
    m_data: [40, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__8_value:
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
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__8_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10_value:
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
    m_data: [112, 114, 101, 99, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10_value)
            as *mut crate::leanh::LeanObject,
        6272524648685798834 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13_value:
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
    m_data: [58, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 97, 116, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14_value)
            as *mut crate::leanh::LeanObject,
        11442535297760353691 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__17_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__17_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14_value)
            as *mut crate::leanh::LeanObject,
        1173000376185431034 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__19_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__20_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__19_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__21_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__17_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__20_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__21_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23_value:
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
    m_data: [41, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23_value)
        as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 58, 61, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 101, 114, 109, 95, 43, 43, 95, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject,1718176677342102874 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [43, 43, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__5_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [115, 116, 114, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__5_value) as *mut crate::leanh::LeanObject,9232979286016572671 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [34, 32, 58, 61, 32, 34, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8_value) as *mut crate::leanh::LeanObject,7932075773091973500 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10_value) as *mut crate::leanh::LeanObject,7306243862518720553 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__12_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__12_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [68, 101, 114, 105, 118, 105, 110, 103, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value) as *mut crate::leanh::LeanObject,15755466758005450470 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value) as *mut crate::leanh::LeanObject,15889585904834194529 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__21_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__21_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__23_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__23_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__23_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__27_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__28_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__27_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__29_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__28_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__30_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__29_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__30_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [70, 111, 114, 109, 97, 116, 46, 103, 114, 111, 117, 112, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [70, 111, 114, 109, 97, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 111, 117, 112, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value) as *mut crate::leanh::LeanObject,18438390214131365702 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value) as *mut crate::leanh::LeanObject,15264817703472686535 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value) as *mut crate::leanh::LeanObject,12875137807382502537 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value) as *mut crate::leanh::LeanObject,4788252454237718004 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__40_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__40: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__40_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__41_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__41_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__42_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__41_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__42_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__40_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__42_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [70, 111, 114, 109, 97, 116, 46, 110, 101, 115, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 101, 115, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value) as *mut crate::leanh::LeanObject,18438390214131365702 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value) as *mut crate::leanh::LeanObject,9817194789849102600 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value) as *mut crate::leanh::LeanObject,12875137807382502537 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value) as *mut crate::leanh::LeanObject,16962373429918864051 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__49_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__49: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__49_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__50_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__50: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__50_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__51_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__50_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__51: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__51_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__49_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__51_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [114, 101, 112, 114, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__55_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53_value) as *mut crate::leanh::LeanObject,17530167084477738488 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__55: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__55_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__56_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__55_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__56: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__56_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__56_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 111, 106, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58_value) as *mut crate::leanh::LeanObject,5353940006376281447 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__60_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__60: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__60_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__61_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [34, 95, 34, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__61: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__61_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [34, 44, 34, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__2_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [70, 111, 114, 109, 97, 116, 46, 108, 105, 110, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 105, 110, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value) as *mut crate::leanh::LeanObject,18438390214131365702 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11661214182450261268 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value) as *mut crate::leanh::LeanObject,12875137807382502537 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__4_value) as *mut crate::leanh::LeanObject,3835909780524915047 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__8_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [70, 111, 114, 109, 97, 116, 46, 110, 105, 108, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [110, 105, 108, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value) as *mut crate::leanh::LeanObject,18438390214131365702 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value:
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
            l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16423084728014368341 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value) as *mut crate::leanh::LeanObject,12875137807382502537 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value:
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
            l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        757700198531151910 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__6_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__6_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__5_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__9_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        70, 111, 114, 109, 97, 116, 46, 98, 114, 97, 99, 107, 101, 116, 0,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11_value:
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
    m_data: [98, 114, 97, 99, 107, 101, 116, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value) as *mut crate::leanh::LeanObject,18438390214131365702 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value:
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
            l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11_value)
            as *mut crate::leanh::LeanObject,
        5697833859555668142 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value) as *mut crate::leanh::LeanObject,12875137807382502537 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value:
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
            l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11_value)
            as *mut crate::leanh::LeanObject,
        11477549012722890157 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__14_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__14_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__16_value:
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
    m_data: [34, 123, 32, 34, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__17_value:
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
    m_data: [34, 32, 125, 34, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__18_value:
    crate::leanh::LeanStringObject<65> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 65,
    m_capacity: 65,
    m_length: 64,
    m_data: [
        39, 100, 101, 114, 105, 118, 105, 110, 103, 32, 82, 101, 112, 114, 39, 32, 102, 97, 105,
        108, 101, 100, 44, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 117, 109,
        98, 101, 114, 32, 111, 102, 32, 102, 105, 101, 108, 100, 115, 32, 105, 110, 32, 115, 116,
        114, 117, 99, 116, 117, 114, 101, 0,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__2_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__4_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__5_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [76, 101, 97, 110, 46, 105, 115, 67, 116, 111, 114, 63, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__6_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject,3984140175429830279 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 112, 114, 65, 114, 103, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,15968885672582162308 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__3_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__5_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 101, 114, 109, 77, 97, 120, 95, 112, 114, 101, 99, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__5_value) as *mut crate::leanh::LeanObject,13126842316985079343 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 120, 95, 112, 114, 101, 99, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7839396180116328695 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 120, 116, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value) as *mut crate::leanh::LeanObject,18438390214131365702 as *mut crate::leanh::LeanObject] };
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,4551484708070513531 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value) as *mut crate::leanh::LeanObject,12875137807382502537 as *mut crate::leanh::LeanObject] };
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,17988585327220880128 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__4_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [70, 111, 114, 109, 97, 116, 46, 116, 101, 120, 116, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__6_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__9_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [64, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10_value) as *mut crate::leanh::LeanObject;
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10_value) as *mut crate::leanh::LeanObject,13290931718435096973 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__12_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 116, 99, 104, 65, 108, 116, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__12_value) as *mut crate::leanh::LeanObject;
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__12_value) as *mut crate::leanh::LeanObject,16529391333736644786 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__14_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__15_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__17_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__18_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [82, 101, 112, 114, 46, 97, 100, 100, 65, 112, 112, 80, 97, 114, 101, 110, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__20_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [97, 100, 100, 65, 112, 112, 80, 97, 114, 101, 110, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__20_value) as *mut crate::leanh::LeanObject;
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value) as *mut crate::leanh::LeanObject,15923304685029768128 as *mut crate::leanh::LeanObject] };
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__20_value) as *mut crate::leanh::LeanObject,13913602313421588049 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__22_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__23_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__22_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__27_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24_value) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25_value) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26_value) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__41_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29_value) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__31_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__32_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__50_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__33_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__31_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__32_value) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__33_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__34_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 101, 114, 109, 73, 102, 84, 104, 101, 110, 69, 108, 115, 101, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__34_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__35_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__34_value) as *mut crate::leanh::LeanObject,14296711813398647265 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__35_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__36_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 102, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__37_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 7, m_data: [116, 101, 114, 109, 95, 226, 137, 165, 95, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__37_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__38_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__37_value) as *mut crate::leanh::LeanObject,15256166972235071802 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__38_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__39_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [62, 61, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__39_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__40_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 104, 101, 110, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__40: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__40_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__41_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 117, 109, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__41_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__42_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__41_value) as *mut crate::leanh::LeanObject,6110315075117401315 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__42_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__43_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [49, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__43: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__43_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__44_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 108, 115, 101, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__44: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__44_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__45_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [50, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__45: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__45_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0_value:
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
    m_data: [109, 97, 116, 99, 104, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11514550152210403337 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__2_value:
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
    m_data: [119, 105, 116, 104, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__3_value:
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
    m_data: [109, 97, 116, 99, 104, 65, 108, 116, 115, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__3_value)
            as *mut crate::leanh::LeanObject,
        13242179749370575553 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value:
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
    m_data: [67, 111, 109, 109, 97, 110, 100, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__1_value:
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
    m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8497769072906204829 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__3_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__3_value)
            as *mut crate::leanh::LeanObject,
        14557702332550915328 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__5_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__5_value)
            as *mut crate::leanh::LeanObject,
        2533412339571800130 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [64, 91, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__8_value:
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
    m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__8_value)
            as *mut crate::leanh::LeanObject,
        7499624980761693169 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__10_value:
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
    m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__10_value)
            as *mut crate::leanh::LeanObject,
        7983999284776576032 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__12_value:
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
    m_data: [65, 116, 116, 114, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__13_value:
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
    m_data: [115, 105, 109, 112, 108, 101, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__13_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__12_value)
            as *mut crate::leanh::LeanObject,
        4584992172905639687 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__13_value)
            as *mut crate::leanh::LeanObject,
        3878072352281346923 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15_value:
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
    m_data: [110, 111, 95, 101, 120, 112, 111, 115, 101, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15_value)
            as *mut crate::leanh::LeanObject,
        282208228266294739 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18_value:
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
    m_data: [93, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__19_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__19_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__19_value)
            as *mut crate::leanh::LeanObject,
        9789339221525904376 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [100, 101, 102, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__22_value:
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
    m_data: [100, 101, 99, 108, 73, 100, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__22_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__22_value)
            as *mut crate::leanh::LeanObject,
        1827444229220621555 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__24_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__24_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__24_value)
            as *mut crate::leanh::LeanObject,
        5473625859156281626 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__26_value:
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
    m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__26_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__26_value)
            as *mut crate::leanh::LeanObject,
        4498178684837002829 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value) as *mut crate::leanh::LeanObject,18438390214131365702 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value) as *mut crate::leanh::LeanObject,12875137807382502537 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__31_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__32_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__33_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__32_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__31_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__33_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__35_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__35_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__35_value)
            as *mut crate::leanh::LeanObject,
        13585030837571646948 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [58, 61, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__38_value:
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
    m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__38_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__39_value:
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
    m_data: [115, 117, 102, 102, 105, 120, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__39_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__38_value)
            as *mut crate::leanh::LeanObject,
        7625897890118033792 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__39_value)
            as *mut crate::leanh::LeanObject,
        8715860392475343861 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41_value:
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
    m_data: [112, 97, 114, 116, 105, 97, 108, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41_value)
            as *mut crate::leanh::LeanObject,
        14919950218492817255 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0_value:
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
    m_data: [109, 117, 116, 117, 97, 108, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0_value)
            as *mut crate::leanh::LeanObject,
        76928035496447287 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__2_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [101, 110, 100, 0],
};
static mut l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value) as *mut crate::leanh::LeanObject,3113176348997436611 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53_value) as *mut crate::leanh::LeanObject,6646382875965622752 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__1_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__0_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__0_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__0_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__1_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__1_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__1_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__2_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__1_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__2_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__2_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__3_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__2_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__3_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__3_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__3_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value) as *mut crate::leanh::LeanObject,5444244426488757208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value) as *mut crate::leanh::LeanObject,5241190260012038858 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value) as *mut crate::leanh::LeanObject,2547228400745046021 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,1364391926285574352 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value) as *mut crate::leanh::LeanObject,12991100434894643113 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value) as *mut crate::leanh::LeanObject,2804318236955327207 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__10_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value) as *mut crate::leanh::LeanObject,318927784862946785 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__10_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__10_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__11_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__10_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value) as *mut crate::leanh::LeanObject,11067026654443863714 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__11_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__11_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__12_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__12_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__12_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__13_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__11_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__12_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4452165776892334359 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__13_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__13_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__14_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__14_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__14_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__15_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__13_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__14_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5152161236099651538 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__15_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__15_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__16_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__15_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value) as *mut crate::leanh::LeanObject,15575403139184735699 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__16_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__16_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__16_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value) as *mut crate::leanh::LeanObject,3413581897292536389 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__18_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value) as *mut crate::leanh::LeanObject,11475959385481971243 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__18_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__18_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__19_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__18_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value) as *mut crate::leanh::LeanObject,119584983352380048 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__19_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__19_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__20_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__19_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1829928117 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,16788731454146790525 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__20_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__20_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__21_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__21_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__21_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__22_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__20_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__21_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7865048094109047614 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__22_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__22_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__23_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__23_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__23_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__24_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__22_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__23_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13839308135485266354 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__24_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__24_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__25_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__24_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,9643117217549648011 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__25_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__25_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3221_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10;
    v___x_3222_ = l_String_toRawSubstring_x27(v___x_3221_);
    return v___x_3222_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3227_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14;
    v___x_3228_ = l_String_toRawSubstring_x27(v___x_3227_);
    return v___x_3228_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3245_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_3245_;
}
pub unsafe fn l_Lean_Elab_Deriving_Repr_mkReprHeader(
    mut v_indVal_3247_: *mut crate::leanh::LeanObject,
    mut v_a_3248_: *mut crate::leanh::LeanObject,
    mut v_a_3249_: *mut crate::leanh::LeanObject,
    mut v_a_3250_: *mut crate::leanh::LeanObject,
    mut v_a_3251_: *mut crate::leanh::LeanObject,
    mut v_a_3252_: *mut crate::leanh::LeanObject,
    mut v_a_3253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v_ref_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: u8 = 0;
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binders_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_argNames_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_targetNames_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_targetType_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3293_: u8 = 0;
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3304_: u8 = 0;
    let mut v_isSharedCheck_3305_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3255_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1;
                v___x_3256_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3257_ = l_Lean_Elab_Deriving_mkHeader(
                    v___x_3255_,
                    v___x_3256_,
                    v_indVal_3247_,
                    v_a_3248_,
                    v_a_3249_,
                    v_a_3250_,
                    v_a_3251_,
                    v_a_3252_,
                    v_a_3253_,
                );
                if crate::leanh::lean_obj_tag(v___x_3257_) == 0 {
                    v_a_3258_ = crate::leanh::lean_ctor_get(v___x_3257_, 0);
                    v_isSharedCheck_3305_ = (!crate::leanh::lean_is_exclusive(v___x_3257_)) as u8;
                    if v_isSharedCheck_3305_ == 0 {
                        v___x_3260_ = v___x_3257_;
                        v_isShared_3261_ = v_isSharedCheck_3305_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3258_);
                        crate::leanh::lean_dec(v___x_3257_);
                        v___x_3260_ = crate::leanh::lean_box(0);
                        v_isShared_3261_ = v_isSharedCheck_3305_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_3257_;
                }
            }
            1 => {
                v_ref_3262_ = crate::leanh::lean_ctor_get(v_a_3252_, 5);
                v_quotContext_3263_ = crate::leanh::lean_ctor_get(v_a_3252_, 10);
                v_currMacroScope_3264_ = crate::leanh::lean_ctor_get(v_a_3252_, 11);
                v___x_3265_ = 0;
                v___x_3266_ = l_Lean_SourceInfo_fromRef(v_ref_3262_, v___x_3265_);
                v___x_3267_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6;
                v___x_3268_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7;
                crate::leanh::lean_inc_n(v___x_3266_, 7);
                v___x_3269_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3269_, 0, v___x_3266_);
                crate::leanh::lean_ctor_set(v___x_3269_, 1, v___x_3268_);
                v___x_3270_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9;
                v___x_3271_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11_once
                    ),
                    _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11,
                );
                v___x_3272_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12;
                crate::leanh::lean_inc_n(v_currMacroScope_3264_, 2);
                crate::leanh::lean_inc_n(v_quotContext_3263_, 2);
                v___x_3273_ =
                    l_Lean_addMacroScope(v_quotContext_3263_, v___x_3272_, v_currMacroScope_3264_);
                v___x_3274_ = crate::leanh::lean_box(0);
                v___x_3275_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3275_, 0, v___x_3266_);
                crate::leanh::lean_ctor_set(v___x_3275_, 1, v___x_3271_);
                crate::leanh::lean_ctor_set(v___x_3275_, 2, v___x_3273_);
                crate::leanh::lean_ctor_set(v___x_3275_, 3, v___x_3274_);
                v___x_3276_ = l_Lean_Syntax_node1(v___x_3266_, v___x_3270_, v___x_3275_);
                v___x_3277_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13;
                v___x_3278_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3278_, 0, v___x_3266_);
                crate::leanh::lean_ctor_set(v___x_3278_, 1, v___x_3277_);
                v___x_3279_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15_once
                    ),
                    _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15,
                );
                v___x_3280_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16;
                v___x_3281_ =
                    l_Lean_addMacroScope(v_quotContext_3263_, v___x_3280_, v_currMacroScope_3264_);
                v___x_3282_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__21;
                v___x_3283_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3283_, 0, v___x_3266_);
                crate::leanh::lean_ctor_set(v___x_3283_, 1, v___x_3279_);
                crate::leanh::lean_ctor_set(v___x_3283_, 2, v___x_3281_);
                crate::leanh::lean_ctor_set(v___x_3283_, 3, v___x_3282_);
                v___x_3284_ =
                    l_Lean_Syntax_node2(v___x_3266_, v___x_3270_, v___x_3278_, v___x_3283_);
                v___x_3285_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once
                    ),
                    _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22,
                );
                v___x_3286_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3286_, 0, v___x_3266_);
                crate::leanh::lean_ctor_set(v___x_3286_, 1, v___x_3270_);
                crate::leanh::lean_ctor_set(v___x_3286_, 2, v___x_3285_);
                v_binders_3287_ = crate::leanh::lean_ctor_get(v_a_3258_, 0);
                v_argNames_3288_ = crate::leanh::lean_ctor_get(v_a_3258_, 1);
                v_targetNames_3289_ = crate::leanh::lean_ctor_get(v_a_3258_, 2);
                v_targetType_3290_ = crate::leanh::lean_ctor_get(v_a_3258_, 3);
                v_isSharedCheck_3304_ = (!crate::leanh::lean_is_exclusive(v_a_3258_)) as u8;
                if v_isSharedCheck_3304_ == 0 {
                    v___x_3292_ = v_a_3258_;
                    v_isShared_3293_ = v_isSharedCheck_3304_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_targetType_3290_);
                    crate::leanh::lean_inc(v_targetNames_3289_);
                    crate::leanh::lean_inc(v_argNames_3288_);
                    crate::leanh::lean_inc(v_binders_3287_);
                    crate::leanh::lean_dec(v_a_3258_);
                    v___x_3292_ = crate::leanh::lean_box(0);
                    v_isShared_3293_ = v_isSharedCheck_3304_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3294_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23;
                crate::leanh::lean_inc(v___x_3266_);
                v___x_3295_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3295_, 0, v___x_3266_);
                crate::leanh::lean_ctor_set(v___x_3295_, 1, v___x_3294_);
                v___x_3296_ = l_Lean_Syntax_node5(
                    v___x_3266_,
                    v___x_3267_,
                    v___x_3269_,
                    v___x_3276_,
                    v___x_3284_,
                    v___x_3286_,
                    v___x_3295_,
                );
                v___x_3297_ = lean_array_push(v_binders_3287_, v___x_3296_);
                if v_isShared_3293_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3292_, 0, v___x_3297_);
                    v___x_3299_ = v___x_3292_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3303_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3297_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3303_, 1, v_argNames_3288_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3303_, 2, v_targetNames_3289_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3303_, 3, v_targetType_3290_);
                    v___x_3299_ = v_reuseFailAlloc_3303_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3261_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3260_, 0, v___x_3299_);
                    v___x_3301_ = v___x_3260_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3302_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3299_);
                    v___x_3301_ = v_reuseFailAlloc_3302_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3301_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_Repr_mkReprHeader___boxed(
    mut v_indVal_3306_: *mut crate::leanh::LeanObject,
    mut v_a_3307_: *mut crate::leanh::LeanObject,
    mut v_a_3308_: *mut crate::leanh::LeanObject,
    mut v_a_3309_: *mut crate::leanh::LeanObject,
    mut v_a_3310_: *mut crate::leanh::LeanObject,
    mut v_a_3311_: *mut crate::leanh::LeanObject,
    mut v_a_3312_: *mut crate::leanh::LeanObject,
    mut v_a_3313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3314_ = l_Lean_Elab_Deriving_Repr_mkReprHeader(
        v_indVal_3306_,
        v_a_3307_,
        v_a_3308_,
        v_a_3309_,
        v_a_3310_,
        v_a_3311_,
        v_a_3312_,
    );
    crate::leanh::lean_dec(v_a_3312_);
    crate::leanh::lean_dec_ref(v_a_3311_);
    crate::leanh::lean_dec(v_a_3310_);
    crate::leanh::lean_dec_ref(v_a_3309_);
    crate::leanh::lean_dec(v_a_3308_);
    crate::leanh::lean_dec_ref(v_a_3307_);
    return v_res_3314_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0(
    mut v_k_3315_: *mut crate::leanh::LeanObject,
    mut v___y_3316_: *mut crate::leanh::LeanObject,
    mut v___y_3317_: *mut crate::leanh::LeanObject,
    mut v_b_3318_: *mut crate::leanh::LeanObject,
    mut v_c_3319_: *mut crate::leanh::LeanObject,
    mut v___y_3320_: *mut crate::leanh::LeanObject,
    mut v___y_3321_: *mut crate::leanh::LeanObject,
    mut v___y_3322_: *mut crate::leanh::LeanObject,
    mut v___y_3323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_3323_);
    crate::leanh::lean_inc_ref(v___y_3322_);
    crate::leanh::lean_inc(v___y_3321_);
    crate::leanh::lean_inc_ref(v___y_3320_);
    crate::leanh::lean_inc(v___y_3317_);
    crate::leanh::lean_inc_ref(v___y_3316_);
    v___x_3325_ = crate::leanh::lean_apply_9(
        v_k_3315_,
        v_b_3318_,
        v_c_3319_,
        v___y_3316_,
        v___y_3317_,
        v___y_3320_,
        v___y_3321_,
        v___y_3322_,
        v___y_3323_,
        crate::leanh::lean_box(0),
    );
    return v___x_3325_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0___boxed(
    mut v_k_3326_: *mut crate::leanh::LeanObject,
    mut v___y_3327_: *mut crate::leanh::LeanObject,
    mut v___y_3328_: *mut crate::leanh::LeanObject,
    mut v_b_3329_: *mut crate::leanh::LeanObject,
    mut v_c_3330_: *mut crate::leanh::LeanObject,
    mut v___y_3331_: *mut crate::leanh::LeanObject,
    mut v___y_3332_: *mut crate::leanh::LeanObject,
    mut v___y_3333_: *mut crate::leanh::LeanObject,
    mut v___y_3334_: *mut crate::leanh::LeanObject,
    mut v___y_3335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3336_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0(v_k_3326_, v___y_3327_, v___y_3328_, v_b_3329_, v_c_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
    crate::leanh::lean_dec(v___y_3334_);
    crate::leanh::lean_dec_ref(v___y_3333_);
    crate::leanh::lean_dec(v___y_3332_);
    crate::leanh::lean_dec_ref(v___y_3331_);
    crate::leanh::lean_dec(v___y_3328_);
    crate::leanh::lean_dec_ref(v___y_3327_);
    return v_res_3336_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(
    mut v_type_3337_: *mut crate::leanh::LeanObject,
    mut v_k_3338_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3339_: u8,
    mut v_whnfType_3340_: u8,
    mut v___y_3341_: *mut crate::leanh::LeanObject,
    mut v___y_3342_: *mut crate::leanh::LeanObject,
    mut v___y_3343_: *mut crate::leanh::LeanObject,
    mut v___y_3344_: *mut crate::leanh::LeanObject,
    mut v___y_3345_: *mut crate::leanh::LeanObject,
    mut v___y_3346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3353_: u8 = 0;
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_3342_);
                crate::leanh::lean_inc_ref(v___y_3341_);
                v___f_3348_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                crate::leanh::lean_closure_set(v___f_3348_, 0, v_k_3338_);
                crate::leanh::lean_closure_set(v___f_3348_, 1, v___y_3341_);
                crate::leanh::lean_closure_set(v___f_3348_, 2, v___y_3342_);
                v___x_3349_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    crate::leanh::lean_box(0),
                    v_type_3337_,
                    v___f_3348_,
                    v_cleanupAnnotations_3339_,
                    v_whnfType_3340_,
                    v___y_3343_,
                    v___y_3344_,
                    v___y_3345_,
                    v___y_3346_,
                );
                if crate::leanh::lean_obj_tag(v___x_3349_) == 0 {
                    return v___x_3349_;
                } else {
                    v_a_3350_ = crate::leanh::lean_ctor_get(v___x_3349_, 0);
                    v_isSharedCheck_3357_ = (!crate::leanh::lean_is_exclusive(v___x_3349_)) as u8;
                    if v_isSharedCheck_3357_ == 0 {
                        v___x_3352_ = v___x_3349_;
                        v_isShared_3353_ = v_isSharedCheck_3357_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3350_);
                        crate::leanh::lean_dec(v___x_3349_);
                        v___x_3352_ = crate::leanh::lean_box(0);
                        v_isShared_3353_ = v_isSharedCheck_3357_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3353_ == 0 {
                    v___x_3355_ = v___x_3352_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3356_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
                    v___x_3355_ = v_reuseFailAlloc_3356_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___boxed(
    mut v_type_3358_: *mut crate::leanh::LeanObject,
    mut v_k_3359_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3360_: *mut crate::leanh::LeanObject,
    mut v_whnfType_3361_: *mut crate::leanh::LeanObject,
    mut v___y_3362_: *mut crate::leanh::LeanObject,
    mut v___y_3363_: *mut crate::leanh::LeanObject,
    mut v___y_3364_: *mut crate::leanh::LeanObject,
    mut v___y_3365_: *mut crate::leanh::LeanObject,
    mut v___y_3366_: *mut crate::leanh::LeanObject,
    mut v___y_3367_: *mut crate::leanh::LeanObject,
    mut v___y_3368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3369_: u8 = 0;
    let mut v_whnfType_boxed_3370_: u8 = 0;
    let mut v_res_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3369_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_3360_) as u8);
    v_whnfType_boxed_3370_ = (crate::leanh::lean_unbox(v_whnfType_3361_) as u8);
    v_res_3371_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(v_type_3358_, v_k_3359_, v_cleanupAnnotations_boxed_3369_, v_whnfType_boxed_3370_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
    crate::leanh::lean_dec(v___y_3367_);
    crate::leanh::lean_dec_ref(v___y_3366_);
    crate::leanh::lean_dec(v___y_3365_);
    crate::leanh::lean_dec_ref(v___y_3364_);
    crate::leanh::lean_dec(v___y_3363_);
    crate::leanh::lean_dec_ref(v___y_3362_);
    return v_res_3371_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4(
    mut v_00_u03b1_3372_: *mut crate::leanh::LeanObject,
    mut v_type_3373_: *mut crate::leanh::LeanObject,
    mut v_k_3374_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3375_: u8,
    mut v_whnfType_3376_: u8,
    mut v___y_3377_: *mut crate::leanh::LeanObject,
    mut v___y_3378_: *mut crate::leanh::LeanObject,
    mut v___y_3379_: *mut crate::leanh::LeanObject,
    mut v___y_3380_: *mut crate::leanh::LeanObject,
    mut v___y_3381_: *mut crate::leanh::LeanObject,
    mut v___y_3382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3384_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(v_type_3373_, v_k_3374_, v_cleanupAnnotations_3375_, v_whnfType_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
    return v___x_3384_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___boxed(
    mut v_00_u03b1_3385_: *mut crate::leanh::LeanObject,
    mut v_type_3386_: *mut crate::leanh::LeanObject,
    mut v_k_3387_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3388_: *mut crate::leanh::LeanObject,
    mut v_whnfType_3389_: *mut crate::leanh::LeanObject,
    mut v___y_3390_: *mut crate::leanh::LeanObject,
    mut v___y_3391_: *mut crate::leanh::LeanObject,
    mut v___y_3392_: *mut crate::leanh::LeanObject,
    mut v___y_3393_: *mut crate::leanh::LeanObject,
    mut v___y_3394_: *mut crate::leanh::LeanObject,
    mut v___y_3395_: *mut crate::leanh::LeanObject,
    mut v___y_3396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3397_: u8 = 0;
    let mut v_whnfType_boxed_3398_: u8 = 0;
    let mut v_res_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3397_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_3388_) as u8);
    v_whnfType_boxed_3398_ = (crate::leanh::lean_unbox(v_whnfType_3389_) as u8);
    v_res_3399_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4(v_00_u03b1_3385_, v_type_3386_, v_k_3387_, v_cleanupAnnotations_boxed_3397_, v_whnfType_boxed_3398_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_);
    crate::leanh::lean_dec(v___y_3395_);
    crate::leanh::lean_dec_ref(v___y_3394_);
    crate::leanh::lean_dec(v___y_3393_);
    crate::leanh::lean_dec_ref(v___y_3392_);
    crate::leanh::lean_dec(v___y_3391_);
    crate::leanh::lean_dec_ref(v___y_3390_);
    return v_res_3399_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3400_ = crate::leanh::lean_box(1);
    v___x_3401_ = l_Lean_MessageData_ofFormat(v___x_3400_);
    return v___x_3401_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3405_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__2;
    v___x_3406_ = l_Lean_MessageData_ofFormat(v___x_3405_);
    return v___x_3406_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8(
    mut v_x_3407_: *mut crate::leanh::LeanObject,
    mut v_x_3408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3413_: u8 = 0;
    let mut v_before_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3417_: u8 = 0;
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3430_: u8 = 0;
    let mut v_unused_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3432_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3408_) == 0 {
                    return v_x_3407_;
                } else {
                    v_head_3409_ = crate::leanh::lean_ctor_get(v_x_3408_, 0);
                    v_tail_3410_ = crate::leanh::lean_ctor_get(v_x_3408_, 1);
                    v_isSharedCheck_3432_ = (!crate::leanh::lean_is_exclusive(v_x_3408_)) as u8;
                    if v_isSharedCheck_3432_ == 0 {
                        v___x_3412_ = v_x_3408_;
                        v_isShared_3413_ = v_isSharedCheck_3432_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3410_);
                        crate::leanh::lean_inc(v_head_3409_);
                        crate::leanh::lean_dec(v_x_3408_);
                        v___x_3412_ = crate::leanh::lean_box(0);
                        v_isShared_3413_ = v_isSharedCheck_3432_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_3414_ = crate::leanh::lean_ctor_get(v_head_3409_, 0);
                v_isSharedCheck_3430_ = (!crate::leanh::lean_is_exclusive(v_head_3409_)) as u8;
                if v_isSharedCheck_3430_ == 0 {
                    v_unused_3431_ = crate::leanh::lean_ctor_get(v_head_3409_, 1);
                    crate::leanh::lean_dec(v_unused_3431_);
                    v___x_3416_ = v_head_3409_;
                    v_isShared_3417_ = v_isSharedCheck_3430_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_3414_);
                    crate::leanh::lean_dec(v_head_3409_);
                    v___x_3416_ = crate::leanh::lean_box(0);
                    v_isShared_3417_ = v_isSharedCheck_3430_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3418_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0);
                if v_isShared_3417_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3416_, 7);
                    crate::leanh::lean_ctor_set(v___x_3416_, 1, v___x_3418_);
                    crate::leanh::lean_ctor_set(v___x_3416_, 0, v_x_3407_);
                    v___x_3420_ = v___x_3416_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3429_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_x_3407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3429_, 1, v___x_3418_);
                    v___x_3420_ = v_reuseFailAlloc_3429_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3421_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3);
                if v_isShared_3413_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3412_, 7);
                    crate::leanh::lean_ctor_set(v___x_3412_, 1, v___x_3421_);
                    crate::leanh::lean_ctor_set(v___x_3412_, 0, v___x_3420_);
                    v___x_3423_ = v___x_3412_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3428_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3420_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3428_, 1, v___x_3421_);
                    v___x_3423_ = v_reuseFailAlloc_3428_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3424_ = l_Lean_MessageData_ofSyntax(v_before_3414_);
                v___x_3425_ = l_Lean_indentD(v___x_3424_);
                v___x_3426_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3426_, 0, v___x_3423_);
                crate::leanh::lean_ctor_set(v___x_3426_, 1, v___x_3425_);
                v_x_3407_ = v___x_3426_;
                v_x_3408_ = v_tail_3410_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7(
    mut v_opts_3433_: *mut crate::leanh::LeanObject,
    mut v_opt_3434_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_3435_ = crate::leanh::lean_ctor_get(v_opt_3434_, 0);
    v_defValue_3436_ = crate::leanh::lean_ctor_get(v_opt_3434_, 1);
    v_map_3437_ = crate::leanh::lean_ctor_get(v_opts_3433_, 0);
    v___x_3438_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3437_,
            v_name_3435_,
        );
    if crate::leanh::lean_obj_tag(v___x_3438_) == 0 {
        let mut v___x_3439_: u8 = 0;
        v___x_3439_ = (crate::leanh::lean_unbox(v_defValue_3436_) as u8);
        return v___x_3439_;
    } else {
        let mut v_val_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3440_ = crate::leanh::lean_ctor_get(v___x_3438_, 0);
        crate::leanh::lean_inc(v_val_3440_);
        crate::leanh::lean_dec_ref_known(v___x_3438_, 1);
        if crate::leanh::lean_obj_tag(v_val_3440_) == 1 {
            let mut v_v_3441_: u8 = 0;
            v_v_3441_ = crate::leanh::lean_ctor_get_uint8(v_val_3440_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_3440_, 0);
            return v_v_3441_;
        } else {
            let mut v___x_3442_: u8 = 0;
            crate::leanh::lean_dec(v_val_3440_);
            v___x_3442_ = (crate::leanh::lean_unbox(v_defValue_3436_) as u8);
            return v___x_3442_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7___boxed(
    mut v_opts_3443_: *mut crate::leanh::LeanObject,
    mut v_opt_3444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3445_: u8 = 0;
    let mut v_r_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3445_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7(v_opts_3443_, v_opt_3444_);
    crate::leanh::lean_dec_ref(v_opt_3444_);
    crate::leanh::lean_dec_ref(v_opts_3443_);
    v_r_3446_ = crate::leanh::lean_box((v_res_3445_) as usize);
    return v_r_3446_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3450_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__1;
    v___x_3451_ = l_Lean_MessageData_ofFormat(v___x_3450_);
    return v___x_3451_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg(
    mut v_msgData_3452_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3453_: *mut crate::leanh::LeanObject,
    mut v___y_3454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: u8 = 0;
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3465_: u8 = 0;
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3477_: u8 = 0;
    let mut v_unused_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3456_ = crate::leanh::lean_ctor_get(v___y_3454_, 2);
                v___x_3457_ = l_Lean_Elab_pp_macroStack;
                v___x_3458_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7(v_options_3456_, v___x_3457_);
                if v___x_3458_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_3453_);
                    v___x_3459_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3459_, 0, v_msgData_3452_);
                    return v___x_3459_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_3453_) == 0 {
                        v___x_3460_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3460_, 0, v_msgData_3452_);
                        return v___x_3460_;
                    } else {
                        v_head_3461_ = crate::leanh::lean_ctor_get(v_macroStack_3453_, 0);
                        crate::leanh::lean_inc(v_head_3461_);
                        v_after_3462_ = crate::leanh::lean_ctor_get(v_head_3461_, 1);
                        v_isSharedCheck_3477_ =
                            (!crate::leanh::lean_is_exclusive(v_head_3461_)) as u8;
                        if v_isSharedCheck_3477_ == 0 {
                            v_unused_3478_ = crate::leanh::lean_ctor_get(v_head_3461_, 0);
                            crate::leanh::lean_dec(v_unused_3478_);
                            v___x_3464_ = v_head_3461_;
                            v_isShared_3465_ = v_isSharedCheck_3477_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_3462_);
                            crate::leanh::lean_dec(v_head_3461_);
                            v___x_3464_ = crate::leanh::lean_box(0);
                            v_isShared_3465_ = v_isSharedCheck_3477_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3466_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0);
                if v_isShared_3465_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3464_, 7);
                    crate::leanh::lean_ctor_set(v___x_3464_, 1, v___x_3466_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 0, v_msgData_3452_);
                    v___x_3468_ = v___x_3464_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3476_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_msgData_3452_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3476_, 1, v___x_3466_);
                    v___x_3468_ = v_reuseFailAlloc_3476_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3469_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2);
                v___x_3470_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3470_, 0, v___x_3468_);
                crate::leanh::lean_ctor_set(v___x_3470_, 1, v___x_3469_);
                v___x_3471_ = l_Lean_MessageData_ofSyntax(v_after_3462_);
                v___x_3472_ = l_Lean_indentD(v___x_3471_);
                v_msgData_3473_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_3473_, 0, v___x_3470_);
                crate::leanh::lean_ctor_set(v_msgData_3473_, 1, v___x_3472_);
                v___x_3474_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8(v_msgData_3473_, v_macroStack_3453_);
                v___x_3475_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3475_, 0, v___x_3474_);
                return v___x_3475_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___boxed(
    mut v_msgData_3479_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3480_: *mut crate::leanh::LeanObject,
    mut v___y_3481_: *mut crate::leanh::LeanObject,
    mut v___y_3482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3483_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg(v_msgData_3479_, v_macroStack_3480_, v___y_3481_);
    crate::leanh::lean_dec_ref(v___y_3481_);
    return v_res_3483_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4(
    mut v_msgData_3484_: *mut crate::leanh::LeanObject,
    mut v___y_3485_: *mut crate::leanh::LeanObject,
    mut v___y_3486_: *mut crate::leanh::LeanObject,
    mut v___y_3487_: *mut crate::leanh::LeanObject,
    mut v___y_3488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3490_ = lean_st_ref_get(v___y_3488_);
    v_env_3491_ = crate::leanh::lean_ctor_get(v___x_3490_, 0);
    crate::leanh::lean_inc_ref(v_env_3491_);
    crate::leanh::lean_dec(v___x_3490_);
    v___x_3492_ = lean_st_ref_get(v___y_3486_);
    v_mctx_3493_ = crate::leanh::lean_ctor_get(v___x_3492_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3493_);
    crate::leanh::lean_dec(v___x_3492_);
    v_lctx_3494_ = crate::leanh::lean_ctor_get(v___y_3485_, 2);
    v_options_3495_ = crate::leanh::lean_ctor_get(v___y_3487_, 2);
    crate::leanh::lean_inc_ref(v_options_3495_);
    crate::leanh::lean_inc_ref(v_lctx_3494_);
    v___x_3496_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3496_, 0, v_env_3491_);
    crate::leanh::lean_ctor_set(v___x_3496_, 1, v_mctx_3493_);
    crate::leanh::lean_ctor_set(v___x_3496_, 2, v_lctx_3494_);
    crate::leanh::lean_ctor_set(v___x_3496_, 3, v_options_3495_);
    v___x_3497_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3497_, 0, v___x_3496_);
    crate::leanh::lean_ctor_set(v___x_3497_, 1, v_msgData_3484_);
    v___x_3498_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3498_, 0, v___x_3497_);
    return v___x_3498_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4___boxed(
    mut v_msgData_3499_: *mut crate::leanh::LeanObject,
    mut v___y_3500_: *mut crate::leanh::LeanObject,
    mut v___y_3501_: *mut crate::leanh::LeanObject,
    mut v___y_3502_: *mut crate::leanh::LeanObject,
    mut v___y_3503_: *mut crate::leanh::LeanObject,
    mut v___y_3504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3505_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4(v_msgData_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
    crate::leanh::lean_dec(v___y_3503_);
    crate::leanh::lean_dec_ref(v___y_3502_);
    crate::leanh::lean_dec(v___y_3501_);
    crate::leanh::lean_dec_ref(v___y_3500_);
    return v_res_3505_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(
    mut v_msg_3506_: *mut crate::leanh::LeanObject,
    mut v___y_3507_: *mut crate::leanh::LeanObject,
    mut v___y_3508_: *mut crate::leanh::LeanObject,
    mut v___y_3509_: *mut crate::leanh::LeanObject,
    mut v___y_3510_: *mut crate::leanh::LeanObject,
    mut v___y_3511_: *mut crate::leanh::LeanObject,
    mut v___y_3512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3523_: u8 = 0;
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3514_ = crate::leanh::lean_ctor_get(v___y_3511_, 5);
                v___x_3515_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4(v_msg_3506_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
                v_a_3516_ = crate::leanh::lean_ctor_get(v___x_3515_, 0);
                crate::leanh::lean_inc(v_a_3516_);
                crate::leanh::lean_dec_ref(v___x_3515_);
                v_macroStack_3517_ = crate::leanh::lean_ctor_get(v___y_3507_, 1);
                v___x_3518_ = l_Lean_Elab_getBetterRef(v_ref_3514_, v_macroStack_3517_);
                crate::leanh::lean_inc(v_macroStack_3517_);
                v___x_3519_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg(v_a_3516_, v_macroStack_3517_, v___y_3511_);
                v_a_3520_ = crate::leanh::lean_ctor_get(v___x_3519_, 0);
                v_isSharedCheck_3528_ = (!crate::leanh::lean_is_exclusive(v___x_3519_)) as u8;
                if v_isSharedCheck_3528_ == 0 {
                    v___x_3522_ = v___x_3519_;
                    v_isShared_3523_ = v_isSharedCheck_3528_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3520_);
                    crate::leanh::lean_dec(v___x_3519_);
                    v___x_3522_ = crate::leanh::lean_box(0);
                    v_isShared_3523_ = v_isSharedCheck_3528_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3524_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3524_, 0, v___x_3518_);
                crate::leanh::lean_ctor_set(v___x_3524_, 1, v_a_3520_);
                if v_isShared_3523_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3522_, 1);
                    crate::leanh::lean_ctor_set(v___x_3522_, 0, v___x_3524_);
                    v___x_3526_ = v___x_3522_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3527_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
                    v___x_3526_ = v_reuseFailAlloc_3527_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3526_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg___boxed(
    mut v_msg_3529_: *mut crate::leanh::LeanObject,
    mut v___y_3530_: *mut crate::leanh::LeanObject,
    mut v___y_3531_: *mut crate::leanh::LeanObject,
    mut v___y_3532_: *mut crate::leanh::LeanObject,
    mut v___y_3533_: *mut crate::leanh::LeanObject,
    mut v___y_3534_: *mut crate::leanh::LeanObject,
    mut v___y_3535_: *mut crate::leanh::LeanObject,
    mut v___y_3536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3537_ =
        l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(
            v_msg_3529_,
            v___y_3530_,
            v___y_3531_,
            v___y_3532_,
            v___y_3533_,
            v___y_3534_,
            v___y_3535_,
        );
    crate::leanh::lean_dec(v___y_3535_);
    crate::leanh::lean_dec_ref(v___y_3534_);
    crate::leanh::lean_dec(v___y_3533_);
    crate::leanh::lean_dec_ref(v___y_3532_);
    crate::leanh::lean_dec(v___y_3531_);
    crate::leanh::lean_dec_ref(v___y_3530_);
    return v_res_3537_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(
    mut v___x_3538_: *mut crate::leanh::LeanObject,
    mut v___x_3539_: *mut crate::leanh::LeanObject,
    mut v_a_3540_: *mut crate::leanh::LeanObject,
    mut v_b_3541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: u8 = 0;
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_3542_ = crate::leanh::lean_ctor_get(v___x_3538_, 1);
                v_endExclusive_3543_ = crate::leanh::lean_ctor_get(v___x_3538_, 2);
                v___x_3544_ = lean_nat_sub(v_endExclusive_3543_, v_startInclusive_3542_);
                v___x_3545_ = lean_nat_dec_eq(v_a_3540_, v___x_3544_);
                crate::leanh::lean_dec(v___x_3544_);
                if v___x_3545_ == 0 {
                    v___x_3546_ = lean_string_utf8_next_fast(v___x_3539_, v_a_3540_);
                    crate::leanh::lean_dec(v_a_3540_);
                    v___x_3547_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3548_ = lean_nat_add(v_b_3541_, v___x_3547_);
                    crate::leanh::lean_dec(v_b_3541_);
                    v_a_3540_ = v___x_3546_;
                    v_b_3541_ = v___x_3548_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_3540_);
                    return v_b_3541_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___boxed(
    mut v___x_3550_: *mut crate::leanh::LeanObject,
    mut v___x_3551_: *mut crate::leanh::LeanObject,
    mut v_a_3552_: *mut crate::leanh::LeanObject,
    mut v_b_3553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3554_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(v___x_3550_, v___x_3551_, v_a_3552_, v_b_3553_);
    crate::leanh::lean_dec_ref(v___x_3551_);
    crate::leanh::lean_dec_ref(v___x_3550_);
    return v_res_3554_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3556_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__0;
    v___x_3557_ = lean_string_utf8_byte_size(v___x_3556_);
    return v___x_3557_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3582_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14;
    v___x_3583_ = l_String_toRawSubstring_x27(v___x_3582_);
    return v___x_3583_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3629_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34;
    v___x_3630_ = l_String_toRawSubstring_x27(v___x_3629_);
    return v___x_3630_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3652_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44;
    v___x_3653_ = l_String_toRawSubstring_x27(v___x_3652_);
    return v___x_3653_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3674_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53;
    v___x_3675_ = l_String_toRawSubstring_x27(v___x_3674_);
    return v___x_3675_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1(
    mut v___f_3692_: *mut crate::leanh::LeanObject,
    mut v___x_3693_: *mut crate::leanh::LeanObject,
    mut v___x_3694_: *mut crate::leanh::LeanObject,
    mut v___x_3695_: *mut crate::leanh::LeanObject,
    mut v___x_3696_: *mut crate::leanh::LeanObject,
    mut v___x_3697_: *mut crate::leanh::LeanObject,
    mut v___x_3698_: *mut crate::leanh::LeanObject,
    mut v___x_3699_: *mut crate::leanh::LeanObject,
    mut v_____r_3700_: *mut crate::leanh::LeanObject,
    mut v_fields_3701_: *mut crate::leanh::LeanObject,
    mut v___y_3702_: *mut crate::leanh::LeanObject,
    mut v___y_3703_: *mut crate::leanh::LeanObject,
    mut v___y_3704_: *mut crate::leanh::LeanObject,
    mut v___y_3705_: *mut crate::leanh::LeanObject,
    mut v___y_3706_: *mut crate::leanh::LeanObject,
    mut v___y_3707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: u8 = 0;
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3717_: u8 = 0;
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3788_: u8 = 0;
    let mut v_a_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3792_: u8 = 0;
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3796_: u8 = 0;
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3801_: u8 = 0;
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3819_: u8 = 0;
    let mut v_a_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3823_: u8 = 0;
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3827_: u8 = 0;
    let mut v_a_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3831_: u8 = 0;
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3835_: u8 = 0;
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: u8 = 0;
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v___x_3699_);
                v___x_3836_ = l_Lean_Meta_isType(
                    v___x_3699_,
                    v___y_3704_,
                    v___y_3705_,
                    v___y_3706_,
                    v___y_3707_,
                );
                if crate::leanh::lean_obj_tag(v___x_3836_) == 0 {
                    v_a_3837_ = crate::leanh::lean_ctor_get(v___x_3836_, 0);
                    crate::leanh::lean_inc(v_a_3837_);
                    v___x_3838_ = (crate::leanh::lean_unbox(v_a_3837_) as u8);
                    crate::leanh::lean_dec(v_a_3837_);
                    if v___x_3838_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3836_, 1);
                        v___x_3839_ = l_Lean_Meta_isProof(
                            v___x_3699_,
                            v___y_3704_,
                            v___y_3705_,
                            v___y_3706_,
                            v___y_3707_,
                        );
                        v___y_3710_ = v___x_3839_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3699_);
                        v___y_3710_ = v___x_3836_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3699_);
                    v___y_3710_ = v___x_3836_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_3710_) == 0 {
                    v_a_3711_ = crate::leanh::lean_ctor_get(v___y_3710_, 0);
                    crate::leanh::lean_inc(v_a_3711_);
                    crate::leanh::lean_dec_ref_known(v___y_3710_, 1);
                    v___x_3712_ = (crate::leanh::lean_unbox(v_a_3711_) as u8);
                    crate::leanh::lean_dec(v_a_3711_);
                    if v___x_3712_ == 0 {
                        crate::leanh::lean_inc(v___y_3707_);
                        crate::leanh::lean_inc_ref(v___y_3706_);
                        crate::leanh::lean_inc(v___y_3705_);
                        crate::leanh::lean_inc_ref(v___y_3704_);
                        crate::leanh::lean_inc(v___y_3703_);
                        crate::leanh::lean_inc_ref(v___y_3702_);
                        v___x_3713_ = crate::leanh::lean_apply_7(
                            v___f_3692_,
                            v___y_3702_,
                            v___y_3703_,
                            v___y_3704_,
                            v___y_3705_,
                            v___y_3706_,
                            v___y_3707_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_3713_) == 0 {
                            v_a_3714_ = crate::leanh::lean_ctor_get(v___x_3713_, 0);
                            v_isSharedCheck_3788_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3713_)) as u8;
                            if v_isSharedCheck_3788_ == 0 {
                                v___x_3716_ = v___x_3713_;
                                v_isShared_3717_ = v_isSharedCheck_3788_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3714_);
                                crate::leanh::lean_dec(v___x_3713_);
                                v___x_3716_ = crate::leanh::lean_box(0);
                                v_isShared_3717_ = v_isSharedCheck_3788_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fields_3701_);
                            crate::leanh::lean_dec(v___x_3698_);
                            crate::leanh::lean_dec(v___x_3697_);
                            crate::leanh::lean_dec(v___x_3696_);
                            crate::leanh::lean_dec(v___x_3695_);
                            crate::leanh::lean_dec(v___x_3694_);
                            crate::leanh::lean_dec_ref(v___x_3693_);
                            v_a_3789_ = crate::leanh::lean_ctor_get(v___x_3713_, 0);
                            v_isSharedCheck_3796_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3713_)) as u8;
                            if v_isSharedCheck_3796_ == 0 {
                                v___x_3791_ = v___x_3713_;
                                v_isShared_3792_ = v_isSharedCheck_3796_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3789_);
                                crate::leanh::lean_dec(v___x_3713_);
                                v___x_3791_ = crate::leanh::lean_box(0);
                                v_isShared_3792_ = v_isSharedCheck_3796_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3698_);
                        crate::leanh::lean_dec(v___x_3697_);
                        crate::leanh::lean_dec(v___x_3695_);
                        crate::leanh::lean_dec(v___x_3694_);
                        crate::leanh::lean_dec_ref(v___x_3693_);
                        crate::leanh::lean_inc(v___y_3707_);
                        crate::leanh::lean_inc_ref(v___y_3706_);
                        crate::leanh::lean_inc(v___y_3705_);
                        crate::leanh::lean_inc_ref(v___y_3704_);
                        crate::leanh::lean_inc(v___y_3703_);
                        crate::leanh::lean_inc_ref(v___y_3702_);
                        v___x_3797_ = crate::leanh::lean_apply_7(
                            v___f_3692_,
                            v___y_3702_,
                            v___y_3703_,
                            v___y_3704_,
                            v___y_3705_,
                            v___y_3706_,
                            v___y_3707_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_3797_) == 0 {
                            v_a_3798_ = crate::leanh::lean_ctor_get(v___x_3797_, 0);
                            v_isSharedCheck_3819_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3797_)) as u8;
                            if v_isSharedCheck_3819_ == 0 {
                                v___x_3800_ = v___x_3797_;
                                v_isShared_3801_ = v_isSharedCheck_3819_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3798_);
                                crate::leanh::lean_dec(v___x_3797_);
                                v___x_3800_ = crate::leanh::lean_box(0);
                                v_isShared_3801_ = v_isSharedCheck_3819_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fields_3701_);
                            crate::leanh::lean_dec(v___x_3696_);
                            v_a_3820_ = crate::leanh::lean_ctor_get(v___x_3797_, 0);
                            v_isSharedCheck_3827_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3797_)) as u8;
                            if v_isSharedCheck_3827_ == 0 {
                                v___x_3822_ = v___x_3797_;
                                v_isShared_3823_ = v_isSharedCheck_3827_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3820_);
                                crate::leanh::lean_dec(v___x_3797_);
                                v___x_3822_ = crate::leanh::lean_box(0);
                                v_isShared_3823_ = v_isSharedCheck_3827_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fields_3701_);
                    crate::leanh::lean_dec(v___x_3698_);
                    crate::leanh::lean_dec(v___x_3697_);
                    crate::leanh::lean_dec(v___x_3696_);
                    crate::leanh::lean_dec(v___x_3695_);
                    crate::leanh::lean_dec(v___x_3694_);
                    crate::leanh::lean_dec_ref(v___x_3693_);
                    crate::leanh::lean_dec_ref(v___f_3692_);
                    v_a_3828_ = crate::leanh::lean_ctor_get(v___y_3710_, 0);
                    v_isSharedCheck_3835_ = (!crate::leanh::lean_is_exclusive(v___y_3710_)) as u8;
                    if v_isSharedCheck_3835_ == 0 {
                        v___x_3830_ = v___y_3710_;
                        v_isShared_3831_ = v_isSharedCheck_3835_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3828_);
                        crate::leanh::lean_dec(v___y_3710_);
                        v___x_3830_ = crate::leanh::lean_box(0);
                        v_isShared_3831_ = v_isSharedCheck_3835_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3718_ = lean_string_utf8_byte_size(v___x_3693_);
                v_quotContext_3719_ = crate::leanh::lean_ctor_get(v___y_3706_, 10);
                v_currMacroScope_3720_ = crate::leanh::lean_ctor_get(v___y_3706_, 11);
                crate::leanh::lean_inc(v___x_3694_);
                crate::leanh::lean_inc_ref(v___x_3693_);
                v___x_3721_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3721_, 0, v___x_3693_);
                crate::leanh::lean_ctor_set(v___x_3721_, 1, v___x_3694_);
                crate::leanh::lean_ctor_set(v___x_3721_, 2, v___x_3718_);
                v___x_3722_ = l_String_Slice_positions(v___x_3721_);
                v___x_3723_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(v___x_3721_, v___x_3693_, v___x_3722_, v___x_3694_);
                crate::leanh::lean_dec_ref(v___x_3693_);
                crate::leanh::lean_dec_ref_known(v___x_3721_, 3);
                v___x_3724_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1);
                v___x_3725_ = lean_nat_add(v___x_3723_, v___x_3724_);
                crate::leanh::lean_dec(v___x_3723_);
                v___x_3726_ = l_Nat_reprFast(v___x_3725_);
                v___x_3727_ = l_Lean_Syntax_mkNumLit(v___x_3726_, v___x_3695_);
                v___x_3728_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3;
                v___x_3729_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4;
                crate::leanh::lean_inc_n(v_a_3714_, 25);
                v___x_3730_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3730_, 0, v_a_3714_);
                crate::leanh::lean_ctor_set(v___x_3730_, 1, v___x_3729_);
                crate::leanh::lean_inc_ref_n(v___x_3730_, 2);
                v___x_3731_ = l_Lean_Syntax_node3(
                    v_a_3714_,
                    v___x_3728_,
                    v_fields_3701_,
                    v___x_3730_,
                    v___x_3696_,
                );
                v___x_3732_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6;
                v___x_3733_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7;
                v___x_3734_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3734_, 0, v_a_3714_);
                crate::leanh::lean_ctor_set(v___x_3734_, 1, v___x_3733_);
                v___x_3735_ = l_Lean_Syntax_node1(v_a_3714_, v___x_3732_, v___x_3734_);
                v___x_3736_ = l_Lean_Syntax_node3(
                    v_a_3714_,
                    v___x_3728_,
                    v___x_3731_,
                    v___x_3730_,
                    v___x_3735_,
                );
                v___x_3737_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9;
                v___x_3738_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11;
                v___x_3739_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7;
                v___x_3740_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3740_, 0, v_a_3714_);
                crate::leanh::lean_ctor_set(v___x_3740_, 1, v___x_3739_);
                v___x_3741_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13;
                v___x_3742_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15);
                v___x_3743_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_n(v_currMacroScope_3720_, 4);
                crate::leanh::lean_inc_n(v_quotContext_3719_, 4);
                v___x_3744_ =
                    l_Lean_addMacroScope(v_quotContext_3719_, v___x_3743_, v_currMacroScope_3720_);
                v___x_3745_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31;
                v___x_3746_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3746_, 0, v_a_3714_);
                crate::leanh::lean_ctor_set(v___x_3746_, 1, v___x_3742_);
                crate::leanh::lean_ctor_set(v___x_3746_, 2, v___x_3744_);
                crate::leanh::lean_ctor_set(v___x_3746_, 3, v___x_3745_);
                v___x_3747_ = l_Lean_Syntax_node1(v_a_3714_, v___x_3741_, v___x_3746_);
                v___x_3748_ = l_Lean_Syntax_node2(v_a_3714_, v___x_3738_, v___x_3740_, v___x_3747_);
                v___x_3749_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33;
                v___x_3750_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35);
                v___x_3751_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38;
                v___x_3752_ =
                    l_Lean_addMacroScope(v_quotContext_3719_, v___x_3751_, v_currMacroScope_3720_);
                v___x_3753_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43;
                v___x_3754_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3754_, 0, v_a_3714_);
                crate::leanh::lean_ctor_set(v___x_3754_, 1, v___x_3750_);
                crate::leanh::lean_ctor_set(v___x_3754_, 2, v___x_3752_);
                crate::leanh::lean_ctor_set(v___x_3754_, 3, v___x_3753_);
                v___x_3755_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9;
                v___x_3756_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45);
                v___x_3757_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47;
                v___x_3758_ =
                    l_Lean_addMacroScope(v_quotContext_3719_, v___x_3757_, v_currMacroScope_3720_);
                v___x_3759_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52;
                v___x_3760_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3760_, 0, v_a_3714_);
                crate::leanh::lean_ctor_set(v___x_3760_, 1, v___x_3756_);
                crate::leanh::lean_ctor_set(v___x_3760_, 2, v___x_3758_);
                crate::leanh::lean_ctor_set(v___x_3760_, 3, v___x_3759_);
                v___x_3761_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54);
                v___x_3762_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__55;
                v___x_3763_ =
                    l_Lean_addMacroScope(v_quotContext_3719_, v___x_3762_, v_currMacroScope_3720_);
                v___x_3764_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57;
                v___x_3765_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3765_, 0, v_a_3714_);
                crate::leanh::lean_ctor_set(v___x_3765_, 1, v___x_3761_);
                crate::leanh::lean_ctor_set(v___x_3765_, 2, v___x_3763_);
                crate::leanh::lean_ctor_set(v___x_3765_, 3, v___x_3764_);
                v___x_3766_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59;
                v___x_3767_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__60;
                v___x_3768_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3768_, 0, v_a_3714_);
                crate::leanh::lean_ctor_set(v___x_3768_, 1, v___x_3767_);
                v___x_3769_ = lean_mk_syntax_ident(v___x_3697_);
                v___x_3770_ = l_Lean_Syntax_node3(
                    v_a_3714_,
                    v___x_3766_,
                    v___x_3698_,
                    v___x_3768_,
                    v___x_3769_,
                );
                v___x_3771_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23;
                v___x_3772_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3772_, 0, v_a_3714_);
                crate::leanh::lean_ctor_set(v___x_3772_, 1, v___x_3771_);
                crate::leanh::lean_inc_ref_n(v___x_3772_, 3);
                crate::leanh::lean_inc_n(v___x_3748_, 3);
                v___x_3773_ = l_Lean_Syntax_node3(
                    v_a_3714_,
                    v___x_3737_,
                    v___x_3748_,
                    v___x_3770_,
                    v___x_3772_,
                );
                v___x_3774_ = l_Lean_Syntax_node1(v_a_3714_, v___x_3755_, v___x_3773_);
                v___x_3775_ = l_Lean_Syntax_node2(v_a_3714_, v___x_3749_, v___x_3765_, v___x_3774_);
                v___x_3776_ = l_Lean_Syntax_node3(
                    v_a_3714_,
                    v___x_3737_,
                    v___x_3748_,
                    v___x_3775_,
                    v___x_3772_,
                );
                v___x_3777_ = l_Lean_Syntax_node2(v_a_3714_, v___x_3755_, v___x_3727_, v___x_3776_);
                v___x_3778_ = l_Lean_Syntax_node2(v_a_3714_, v___x_3749_, v___x_3760_, v___x_3777_);
                v___x_3779_ = l_Lean_Syntax_node3(
                    v_a_3714_,
                    v___x_3737_,
                    v___x_3748_,
                    v___x_3778_,
                    v___x_3772_,
                );
                v___x_3780_ = l_Lean_Syntax_node1(v_a_3714_, v___x_3755_, v___x_3779_);
                v___x_3781_ = l_Lean_Syntax_node2(v_a_3714_, v___x_3749_, v___x_3754_, v___x_3780_);
                v___x_3782_ = l_Lean_Syntax_node3(
                    v_a_3714_,
                    v___x_3737_,
                    v___x_3748_,
                    v___x_3781_,
                    v___x_3772_,
                );
                v___x_3783_ = l_Lean_Syntax_node3(
                    v_a_3714_,
                    v___x_3728_,
                    v___x_3736_,
                    v___x_3730_,
                    v___x_3782_,
                );
                v___x_3784_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3784_, 0, v___x_3783_);
                if v_isShared_3717_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3716_, 0, v___x_3784_);
                    v___x_3786_ = v___x_3716_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3787_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___x_3784_);
                    v___x_3786_ = v_reuseFailAlloc_3787_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3786_;
            }
            4 => {
                if v_isShared_3792_ == 0 {
                    v___x_3794_ = v___x_3791_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3795_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
                    v___x_3794_ = v_reuseFailAlloc_3795_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3794_;
            }
            6 => {
                v___x_3802_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3;
                v___x_3803_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4;
                crate::leanh::lean_inc_n(v_a_3798_, 7);
                v___x_3804_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3804_, 0, v_a_3798_);
                crate::leanh::lean_ctor_set(v___x_3804_, 1, v___x_3803_);
                crate::leanh::lean_inc_ref_n(v___x_3804_, 2);
                v___x_3805_ = l_Lean_Syntax_node3(
                    v_a_3798_,
                    v___x_3802_,
                    v_fields_3701_,
                    v___x_3804_,
                    v___x_3696_,
                );
                v___x_3806_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6;
                v___x_3807_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7;
                v___x_3808_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3808_, 0, v_a_3798_);
                crate::leanh::lean_ctor_set(v___x_3808_, 1, v___x_3807_);
                v___x_3809_ = l_Lean_Syntax_node1(v_a_3798_, v___x_3806_, v___x_3808_);
                v___x_3810_ = l_Lean_Syntax_node3(
                    v_a_3798_,
                    v___x_3802_,
                    v___x_3805_,
                    v___x_3804_,
                    v___x_3809_,
                );
                v___x_3811_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__61;
                v___x_3812_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3812_, 0, v_a_3798_);
                crate::leanh::lean_ctor_set(v___x_3812_, 1, v___x_3811_);
                v___x_3813_ = l_Lean_Syntax_node1(v_a_3798_, v___x_3806_, v___x_3812_);
                v___x_3814_ = l_Lean_Syntax_node3(
                    v_a_3798_,
                    v___x_3802_,
                    v___x_3810_,
                    v___x_3804_,
                    v___x_3813_,
                );
                v___x_3815_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3815_, 0, v___x_3814_);
                if v_isShared_3801_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3800_, 0, v___x_3815_);
                    v___x_3817_ = v___x_3800_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3818_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3815_);
                    v___x_3817_ = v_reuseFailAlloc_3818_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3817_;
            }
            8 => {
                if v_isShared_3823_ == 0 {
                    v___x_3825_ = v___x_3822_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3826_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3820_);
                    v___x_3825_ = v_reuseFailAlloc_3826_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3825_;
            }
            10 => {
                if v_isShared_3831_ == 0 {
                    v___x_3833_ = v___x_3830_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3834_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
                    v___x_3833_ = v_reuseFailAlloc_3834_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3833_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3840_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_3841_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_3842_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_3843_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_3844_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_3845_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_3846_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_3847_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_____r_3848_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_fields_3849_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_3850_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_3851_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_3852_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3853_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3854_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3855_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3856_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3857_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1(v___f_3840_, v___x_3841_, v___x_3842_, v___x_3843_, v___x_3844_, v___x_3845_, v___x_3846_, v___x_3847_, v_____r_3848_, v_fields_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
    crate::leanh::lean_dec(v___y_3855_);
    crate::leanh::lean_dec_ref(v___y_3854_);
    crate::leanh::lean_dec(v___y_3853_);
    crate::leanh::lean_dec_ref(v___y_3852_);
    crate::leanh::lean_dec(v___y_3851_);
    crate::leanh::lean_dec_ref(v___y_3850_);
    return v_res_3857_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0(
    mut v___y_3858_: *mut crate::leanh::LeanObject,
    mut v___y_3859_: *mut crate::leanh::LeanObject,
    mut v___y_3860_: *mut crate::leanh::LeanObject,
    mut v___y_3861_: *mut crate::leanh::LeanObject,
    mut v___y_3862_: *mut crate::leanh::LeanObject,
    mut v___y_3863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: u8 = 0;
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_3865_ = crate::leanh::lean_ctor_get(v___y_3862_, 5);
    v___x_3866_ = 0;
    v___x_3867_ = l_Lean_SourceInfo_fromRef(v_ref_3865_, v___x_3866_);
    v___x_3868_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3868_, 0, v___x_3867_);
    return v___x_3868_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0___boxed(
    mut v___y_3869_: *mut crate::leanh::LeanObject,
    mut v___y_3870_: *mut crate::leanh::LeanObject,
    mut v___y_3871_: *mut crate::leanh::LeanObject,
    mut v___y_3872_: *mut crate::leanh::LeanObject,
    mut v___y_3873_: *mut crate::leanh::LeanObject,
    mut v___y_3874_: *mut crate::leanh::LeanObject,
    mut v___y_3875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3876_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0(v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
    crate::leanh::lean_dec(v___y_3874_);
    crate::leanh::lean_dec_ref(v___y_3873_);
    crate::leanh::lean_dec(v___y_3872_);
    crate::leanh::lean_dec_ref(v___y_3871_);
    crate::leanh::lean_dec(v___y_3870_);
    crate::leanh::lean_dec_ref(v___y_3869_);
    return v_res_3876_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3880_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__2;
    v___x_3881_ = l_String_toRawSubstring_x27(v___x_3880_);
    return v___x_3881_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(
    mut v_upperBound_3901_: *mut crate::leanh::LeanObject,
    mut v___x_3902_: *mut crate::leanh::LeanObject,
    mut v___x_3903_: *mut crate::leanh::LeanObject,
    mut v_xs_3904_: *mut crate::leanh::LeanObject,
    mut v___x_3905_: *mut crate::leanh::LeanObject,
    mut v_a_3906_: *mut crate::leanh::LeanObject,
    mut v_b_3907_: *mut crate::leanh::LeanObject,
    mut v___y_3908_: *mut crate::leanh::LeanObject,
    mut v___y_3909_: *mut crate::leanh::LeanObject,
    mut v___y_3910_: *mut crate::leanh::LeanObject,
    mut v___y_3911_: *mut crate::leanh::LeanObject,
    mut v___y_3912_: *mut crate::leanh::LeanObject,
    mut v___y_3913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v_a_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3929_: u8 = 0;
    let mut v_a_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3933_: u8 = 0;
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3937_: u8 = 0;
    let mut v___x_3938_: u8 = 0;
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3973_: u8 = 0;
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3977_: u8 = 0;
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3938_ = lean_nat_dec_lt(v_a_3906_, v_upperBound_3901_);
                if v___x_3938_ == 0 {
                    crate::leanh::lean_dec(v_a_3906_);
                    crate::leanh::lean_dec(v___x_3905_);
                    v___x_3939_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3939_, 0, v_b_3907_);
                    return v___x_3939_;
                } else {
                    v___f_3940_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__0;
                    v___x_3941_ = l_Lean_instInhabitedExpr;
                    v___x_3942_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3943_ = lean_array_fget_borrowed(v___x_3902_, v_a_3906_);
                    crate::leanh::lean_inc(v___x_3943_);
                    v___x_3944_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v___x_3943_,
                        v___x_3938_,
                    );
                    v___x_3945_ = crate::leanh::lean_box(2);
                    crate::leanh::lean_inc_ref(v___x_3944_);
                    v___x_3946_ = l_Lean_Syntax_mkStrLit(v___x_3944_, v___x_3945_);
                    v___x_3947_ = lean_nat_add(v___x_3903_, v_a_3906_);
                    v___x_3948_ = lean_array_get_borrowed(v___x_3941_, v_xs_3904_, v___x_3947_);
                    crate::leanh::lean_dec(v___x_3947_);
                    v___x_3949_ = lean_nat_dec_eq(v_a_3906_, v___x_3942_);
                    if v___x_3949_ == 0 {
                        v___x_3950_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0(v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
                        if crate::leanh::lean_obj_tag(v___x_3950_) == 0 {
                            v_a_3951_ = crate::leanh::lean_ctor_get(v___x_3950_, 0);
                            crate::leanh::lean_inc_n(v_a_3951_, 6);
                            crate::leanh::lean_dec_ref_known(v___x_3950_, 1);
                            v_quotContext_3952_ = crate::leanh::lean_ctor_get(v___y_3912_, 10);
                            v_currMacroScope_3953_ = crate::leanh::lean_ctor_get(v___y_3912_, 11);
                            v___x_3954_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3;
                            v___x_3955_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4;
                            v___x_3956_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3956_, 0, v_a_3951_);
                            crate::leanh::lean_ctor_set(v___x_3956_, 1, v___x_3955_);
                            v___x_3957_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6;
                            v___x_3958_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__1;
                            v___x_3959_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3959_, 0, v_a_3951_);
                            crate::leanh::lean_ctor_set(v___x_3959_, 1, v___x_3958_);
                            v___x_3960_ = l_Lean_Syntax_node1(v_a_3951_, v___x_3957_, v___x_3959_);
                            crate::leanh::lean_inc_ref(v___x_3956_);
                            v___x_3961_ = l_Lean_Syntax_node3(
                                v_a_3951_,
                                v___x_3954_,
                                v_b_3907_,
                                v___x_3956_,
                                v___x_3960_,
                            );
                            v___x_3962_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3);
                            v___x_3963_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5;
                            crate::leanh::lean_inc(v_currMacroScope_3953_);
                            crate::leanh::lean_inc(v_quotContext_3952_);
                            v___x_3964_ = l_Lean_addMacroScope(
                                v_quotContext_3952_,
                                v___x_3963_,
                                v_currMacroScope_3953_,
                            );
                            v___x_3965_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10;
                            v___x_3966_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3966_, 0, v_a_3951_);
                            crate::leanh::lean_ctor_set(v___x_3966_, 1, v___x_3962_);
                            crate::leanh::lean_ctor_set(v___x_3966_, 2, v___x_3964_);
                            crate::leanh::lean_ctor_set(v___x_3966_, 3, v___x_3965_);
                            v___x_3967_ = l_Lean_Syntax_node3(
                                v_a_3951_,
                                v___x_3954_,
                                v___x_3961_,
                                v___x_3956_,
                                v___x_3966_,
                            );
                            v___x_3968_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v___x_3948_);
                            crate::leanh::lean_inc(v___x_3905_);
                            crate::leanh::lean_inc(v___x_3943_);
                            v___x_3969_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1(v___f_3940_, v___x_3944_, v___x_3942_, v___x_3945_, v___x_3946_, v___x_3943_, v___x_3905_, v___x_3948_, v___x_3968_, v___x_3967_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
                            v___y_3916_ = v___x_3969_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3946_);
                            crate::leanh::lean_dec_ref(v___x_3944_);
                            crate::leanh::lean_dec(v_b_3907_);
                            crate::leanh::lean_dec(v_a_3906_);
                            crate::leanh::lean_dec(v___x_3905_);
                            v_a_3970_ = crate::leanh::lean_ctor_get(v___x_3950_, 0);
                            v_isSharedCheck_3977_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3950_)) as u8;
                            if v_isSharedCheck_3977_ == 0 {
                                v___x_3972_ = v___x_3950_;
                                v_isShared_3973_ = v_isSharedCheck_3977_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3970_);
                                crate::leanh::lean_dec(v___x_3950_);
                                v___x_3972_ = crate::leanh::lean_box(0);
                                v_isShared_3973_ = v_isSharedCheck_3977_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v___x_3978_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v___x_3948_);
                        crate::leanh::lean_inc(v___x_3905_);
                        crate::leanh::lean_inc(v___x_3943_);
                        v___x_3979_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1(v___f_3940_, v___x_3944_, v___x_3942_, v___x_3945_, v___x_3946_, v___x_3943_, v___x_3905_, v___x_3948_, v___x_3978_, v_b_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
                        v___y_3916_ = v___x_3979_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_3916_) == 0 {
                    v_a_3917_ = crate::leanh::lean_ctor_get(v___y_3916_, 0);
                    v_isSharedCheck_3929_ = (!crate::leanh::lean_is_exclusive(v___y_3916_)) as u8;
                    if v_isSharedCheck_3929_ == 0 {
                        v___x_3919_ = v___y_3916_;
                        v_isShared_3920_ = v_isSharedCheck_3929_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3917_);
                        crate::leanh::lean_dec(v___y_3916_);
                        v___x_3919_ = crate::leanh::lean_box(0);
                        v_isShared_3920_ = v_isSharedCheck_3929_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3906_);
                    crate::leanh::lean_dec(v___x_3905_);
                    v_a_3930_ = crate::leanh::lean_ctor_get(v___y_3916_, 0);
                    v_isSharedCheck_3937_ = (!crate::leanh::lean_is_exclusive(v___y_3916_)) as u8;
                    if v_isSharedCheck_3937_ == 0 {
                        v___x_3932_ = v___y_3916_;
                        v_isShared_3933_ = v_isSharedCheck_3937_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3930_);
                        crate::leanh::lean_dec(v___y_3916_);
                        v___x_3932_ = crate::leanh::lean_box(0);
                        v_isShared_3933_ = v_isSharedCheck_3937_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_3917_) == 0 {
                    crate::leanh::lean_dec(v_a_3906_);
                    crate::leanh::lean_dec(v___x_3905_);
                    v_a_3921_ = crate::leanh::lean_ctor_get(v_a_3917_, 0);
                    crate::leanh::lean_inc(v_a_3921_);
                    crate::leanh::lean_dec_ref_known(v_a_3917_, 1);
                    if v_isShared_3920_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3919_, 0, v_a_3921_);
                        v___x_3923_ = v___x_3919_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3924_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3921_);
                        v___x_3923_ = v_reuseFailAlloc_3924_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3919_);
                    v_a_3925_ = crate::leanh::lean_ctor_get(v_a_3917_, 0);
                    crate::leanh::lean_inc(v_a_3925_);
                    crate::leanh::lean_dec_ref_known(v_a_3917_, 1);
                    v___x_3926_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3927_ = lean_nat_add(v_a_3906_, v___x_3926_);
                    crate::leanh::lean_dec(v_a_3906_);
                    v_a_3906_ = v___x_3927_;
                    v_b_3907_ = v_a_3925_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_3923_;
            }
            4 => {
                if v_isShared_3933_ == 0 {
                    v___x_3935_ = v___x_3932_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3936_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
                    v___x_3935_ = v_reuseFailAlloc_3936_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3935_;
            }
            6 => {
                if v_isShared_3973_ == 0 {
                    v___x_3975_ = v___x_3972_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3976_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_a_3970_);
                    v___x_3975_ = v_reuseFailAlloc_3976_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___boxed(
    mut v_upperBound_3980_: *mut crate::leanh::LeanObject,
    mut v___x_3981_: *mut crate::leanh::LeanObject,
    mut v___x_3982_: *mut crate::leanh::LeanObject,
    mut v_xs_3983_: *mut crate::leanh::LeanObject,
    mut v___x_3984_: *mut crate::leanh::LeanObject,
    mut v_a_3985_: *mut crate::leanh::LeanObject,
    mut v_b_3986_: *mut crate::leanh::LeanObject,
    mut v___y_3987_: *mut crate::leanh::LeanObject,
    mut v___y_3988_: *mut crate::leanh::LeanObject,
    mut v___y_3989_: *mut crate::leanh::LeanObject,
    mut v___y_3990_: *mut crate::leanh::LeanObject,
    mut v___y_3991_: *mut crate::leanh::LeanObject,
    mut v___y_3992_: *mut crate::leanh::LeanObject,
    mut v___y_3993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3994_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(v_upperBound_3980_, v___x_3981_, v___x_3982_, v_xs_3983_, v___x_3984_, v_a_3985_, v_b_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
    crate::leanh::lean_dec(v___y_3992_);
    crate::leanh::lean_dec_ref(v___y_3991_);
    crate::leanh::lean_dec(v___y_3990_);
    crate::leanh::lean_dec_ref(v___y_3989_);
    crate::leanh::lean_dec(v___y_3988_);
    crate::leanh::lean_dec_ref(v___y_3987_);
    crate::leanh::lean_dec_ref(v_xs_3983_);
    crate::leanh::lean_dec(v___x_3982_);
    crate::leanh::lean_dec_ref(v___x_3981_);
    crate::leanh::lean_dec(v_upperBound_3980_);
    return v_res_3994_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3996_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__0;
    v___x_3997_ = l_String_toRawSubstring_x27(v___x_3996_);
    return v___x_3997_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4018_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__9;
    v___x_4019_ = l_String_toRawSubstring_x27(v___x_4018_);
    return v___x_4019_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4037_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__18;
    v___x_4038_ = l_Lean_stringToMessageData(v___x_4037_);
    return v___x_4038_;
}
pub unsafe fn l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0(
    mut v___x_4039_: *mut crate::leanh::LeanObject,
    mut v_numParams_4040_: *mut crate::leanh::LeanObject,
    mut v___x_4041_: *mut crate::leanh::LeanObject,
    mut v___x_4042_: *mut crate::leanh::LeanObject,
    mut v_xs_4043_: *mut crate::leanh::LeanObject,
    mut v_x_4044_: *mut crate::leanh::LeanObject,
    mut v___y_4045_: *mut crate::leanh::LeanObject,
    mut v___y_4046_: *mut crate::leanh::LeanObject,
    mut v___y_4047_: *mut crate::leanh::LeanObject,
    mut v___y_4048_: *mut crate::leanh::LeanObject,
    mut v___y_4049_: *mut crate::leanh::LeanObject,
    mut v___y_4050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: u8 = 0;
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4074_: u8 = 0;
    let mut v_ref_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4098_: u8 = 0;
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: u8 = 0;
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4108_: u8 = 0;
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4112_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4052_ = crate::leanh::lean_ctor_get(v___y_4049_, 5);
                v_quotContext_4053_ = crate::leanh::lean_ctor_get(v___y_4049_, 10);
                v_currMacroScope_4054_ = crate::leanh::lean_ctor_get(v___y_4049_, 11);
                v___x_4055_ = 0;
                v___x_4056_ = l_Lean_SourceInfo_fromRef(v_ref_4052_, v___x_4055_);
                v___x_4057_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1,
                );
                v___x_4058_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3;
                crate::leanh::lean_inc(v_currMacroScope_4054_);
                crate::leanh::lean_inc(v_quotContext_4053_);
                v___x_4059_ =
                    l_Lean_addMacroScope(v_quotContext_4053_, v___x_4058_, v_currMacroScope_4054_);
                v___x_4060_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__8;
                v___x_4061_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4061_, 0, v___x_4056_);
                crate::leanh::lean_ctor_set(v___x_4061_, 1, v___x_4057_);
                crate::leanh::lean_ctor_set(v___x_4061_, 2, v___x_4059_);
                crate::leanh::lean_ctor_set(v___x_4061_, 3, v___x_4060_);
                v___x_4099_ = lean_array_get_size(v_xs_4043_);
                v___x_4100_ = lean_array_get_size(v___x_4039_);
                v___x_4101_ = lean_nat_add(v_numParams_4040_, v___x_4100_);
                v___x_4102_ = lean_nat_dec_eq(v___x_4099_, v___x_4101_);
                crate::leanh::lean_dec(v___x_4101_);
                if v___x_4102_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4061_, 4);
                    crate::leanh::lean_dec(v___x_4042_);
                    crate::leanh::lean_dec(v___x_4041_);
                    v___x_4103_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19_once
                        ),
                        _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19,
                    );
                    v___x_4104_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(v___x_4103_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
                    v_a_4105_ = crate::leanh::lean_ctor_get(v___x_4104_, 0);
                    v_isSharedCheck_4112_ = (!crate::leanh::lean_is_exclusive(v___x_4104_)) as u8;
                    if v_isSharedCheck_4112_ == 0 {
                        v___x_4107_ = v___x_4104_;
                        v_isShared_4108_ = v_isSharedCheck_4112_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4105_);
                        crate::leanh::lean_dec(v___x_4104_);
                        v___x_4107_ = crate::leanh::lean_box(0);
                        v_isShared_4108_ = v_isSharedCheck_4112_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___y_4063_ = v___y_4045_;
                    v___y_4064_ = v___y_4046_;
                    v___y_4065_ = v___y_4047_;
                    v___y_4066_ = v___y_4048_;
                    v___y_4067_ = v___y_4049_;
                    v___y_4068_ = v___y_4050_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4069_ = lean_array_get_size(v___x_4039_);
                v___x_4070_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(v___x_4069_, v___x_4039_, v_numParams_4040_, v_xs_4043_, v___x_4041_, v___x_4042_, v___x_4061_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
                if crate::leanh::lean_obj_tag(v___x_4070_) == 0 {
                    v_a_4071_ = crate::leanh::lean_ctor_get(v___x_4070_, 0);
                    v_isSharedCheck_4098_ = (!crate::leanh::lean_is_exclusive(v___x_4070_)) as u8;
                    if v_isSharedCheck_4098_ == 0 {
                        v___x_4073_ = v___x_4070_;
                        v_isShared_4074_ = v_isSharedCheck_4098_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4071_);
                        crate::leanh::lean_dec(v___x_4070_);
                        v___x_4073_ = crate::leanh::lean_box(0);
                        v_isShared_4074_ = v_isSharedCheck_4098_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_4070_;
                }
            }
            2 => {
                v_ref_4075_ = crate::leanh::lean_ctor_get(v___y_4067_, 5);
                v_quotContext_4076_ = crate::leanh::lean_ctor_get(v___y_4067_, 10);
                v_currMacroScope_4077_ = crate::leanh::lean_ctor_get(v___y_4067_, 11);
                v___x_4078_ = l_Lean_SourceInfo_fromRef(v_ref_4075_, v___x_4055_);
                v___x_4079_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33;
                v___x_4080_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10_once
                    ),
                    _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10,
                );
                v___x_4081_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12;
                crate::leanh::lean_inc(v_currMacroScope_4077_);
                crate::leanh::lean_inc(v_quotContext_4076_);
                v___x_4082_ =
                    l_Lean_addMacroScope(v_quotContext_4076_, v___x_4081_, v_currMacroScope_4077_);
                v___x_4083_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__15;
                crate::leanh::lean_inc_n(v___x_4078_, 6);
                v___x_4084_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4084_, 0, v___x_4078_);
                crate::leanh::lean_ctor_set(v___x_4084_, 1, v___x_4080_);
                crate::leanh::lean_ctor_set(v___x_4084_, 2, v___x_4082_);
                crate::leanh::lean_ctor_set(v___x_4084_, 3, v___x_4083_);
                v___x_4085_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9;
                v___x_4086_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6;
                v___x_4087_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__16;
                v___x_4088_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4088_, 0, v___x_4078_);
                crate::leanh::lean_ctor_set(v___x_4088_, 1, v___x_4087_);
                v___x_4089_ = l_Lean_Syntax_node1(v___x_4078_, v___x_4086_, v___x_4088_);
                v___x_4090_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__17;
                v___x_4091_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4091_, 0, v___x_4078_);
                crate::leanh::lean_ctor_set(v___x_4091_, 1, v___x_4090_);
                v___x_4092_ = l_Lean_Syntax_node1(v___x_4078_, v___x_4086_, v___x_4091_);
                v___x_4093_ = l_Lean_Syntax_node3(
                    v___x_4078_,
                    v___x_4085_,
                    v___x_4089_,
                    v_a_4071_,
                    v___x_4092_,
                );
                v___x_4094_ =
                    l_Lean_Syntax_node2(v___x_4078_, v___x_4079_, v___x_4084_, v___x_4093_);
                if v_isShared_4074_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4073_, 0, v___x_4094_);
                    v___x_4096_ = v___x_4073_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4097_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4097_, 0, v___x_4094_);
                    v___x_4096_ = v_reuseFailAlloc_4097_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4096_;
            }
            4 => {
                if v_isShared_4108_ == 0 {
                    v___x_4110_ = v___x_4107_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4111_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4105_);
                    v___x_4110_ = v_reuseFailAlloc_4111_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4110_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___boxed(
    mut v___x_4113_: *mut crate::leanh::LeanObject,
    mut v_numParams_4114_: *mut crate::leanh::LeanObject,
    mut v___x_4115_: *mut crate::leanh::LeanObject,
    mut v___x_4116_: *mut crate::leanh::LeanObject,
    mut v_xs_4117_: *mut crate::leanh::LeanObject,
    mut v_x_4118_: *mut crate::leanh::LeanObject,
    mut v___y_4119_: *mut crate::leanh::LeanObject,
    mut v___y_4120_: *mut crate::leanh::LeanObject,
    mut v___y_4121_: *mut crate::leanh::LeanObject,
    mut v___y_4122_: *mut crate::leanh::LeanObject,
    mut v___y_4123_: *mut crate::leanh::LeanObject,
    mut v___y_4124_: *mut crate::leanh::LeanObject,
    mut v___y_4125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4126_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0(
        v___x_4113_,
        v_numParams_4114_,
        v___x_4115_,
        v___x_4116_,
        v_xs_4117_,
        v_x_4118_,
        v___y_4119_,
        v___y_4120_,
        v___y_4121_,
        v___y_4122_,
        v___y_4123_,
        v___y_4124_,
    );
    crate::leanh::lean_dec(v___y_4124_);
    crate::leanh::lean_dec_ref(v___y_4123_);
    crate::leanh::lean_dec(v___y_4122_);
    crate::leanh::lean_dec_ref(v___y_4121_);
    crate::leanh::lean_dec(v___y_4120_);
    crate::leanh::lean_dec_ref(v___y_4119_);
    crate::leanh::lean_dec_ref(v_x_4118_);
    crate::leanh::lean_dec_ref(v_xs_4117_);
    crate::leanh::lean_dec(v_numParams_4114_);
    crate::leanh::lean_dec_ref(v___x_4113_);
    return v_res_4126_;
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4127_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_4127_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0(
    mut v_msg_4134_: *mut crate::leanh::LeanObject,
    mut v___y_4135_: *mut crate::leanh::LeanObject,
    mut v___y_4136_: *mut crate::leanh::LeanObject,
    mut v___y_4137_: *mut crate::leanh::LeanObject,
    mut v___y_4138_: *mut crate::leanh::LeanObject,
    mut v___y_4139_: *mut crate::leanh::LeanObject,
    mut v___y_4140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4147_: u8 = 0;
    let mut v_toFunctor_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4154_: u8 = 0;
    let mut v___f_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4171_: u8 = 0;
    let mut v_toFunctor_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4178_: u8 = 0;
    let mut v___f_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4195_: u8 = 0;
    let mut v_toFunctor_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4202_: u8 = 0;
    let mut v___f_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_19815__overap_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4221_: u8 = 0;
    let mut v_unused_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4223_: u8 = 0;
    let mut v_unused_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4227_: u8 = 0;
    let mut v_unused_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4229_: u8 = 0;
    let mut v_unused_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut v_unused_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4235_: u8 = 0;
    let mut v_unused_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4142_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0);
                v___x_4143_ = l_StateRefT_x27_instMonad___redArg(v___x_4142_);
                v_toApplicative_4144_ = crate::leanh::lean_ctor_get(v___x_4143_, 0);
                v_isSharedCheck_4235_ = (!crate::leanh::lean_is_exclusive(v___x_4143_)) as u8;
                if v_isSharedCheck_4235_ == 0 {
                    v_unused_4236_ = crate::leanh::lean_ctor_get(v___x_4143_, 1);
                    crate::leanh::lean_dec(v_unused_4236_);
                    v___x_4146_ = v___x_4143_;
                    v_isShared_4147_ = v_isSharedCheck_4235_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_4144_);
                    crate::leanh::lean_dec(v___x_4143_);
                    v___x_4146_ = crate::leanh::lean_box(0);
                    v_isShared_4147_ = v_isSharedCheck_4235_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4148_ = crate::leanh::lean_ctor_get(v_toApplicative_4144_, 0);
                v_toSeq_4149_ = crate::leanh::lean_ctor_get(v_toApplicative_4144_, 2);
                v_toSeqLeft_4150_ = crate::leanh::lean_ctor_get(v_toApplicative_4144_, 3);
                v_toSeqRight_4151_ = crate::leanh::lean_ctor_get(v_toApplicative_4144_, 4);
                v_isSharedCheck_4233_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_4144_)) as u8;
                if v_isSharedCheck_4233_ == 0 {
                    v_unused_4234_ = crate::leanh::lean_ctor_get(v_toApplicative_4144_, 1);
                    crate::leanh::lean_dec(v_unused_4234_);
                    v___x_4153_ = v_toApplicative_4144_;
                    v_isShared_4154_ = v_isSharedCheck_4233_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_4151_);
                    crate::leanh::lean_inc(v_toSeqLeft_4150_);
                    crate::leanh::lean_inc(v_toSeq_4149_);
                    crate::leanh::lean_inc(v_toFunctor_4148_);
                    crate::leanh::lean_dec(v_toApplicative_4144_);
                    v___x_4153_ = crate::leanh::lean_box(0);
                    v_isShared_4154_ = v_isSharedCheck_4233_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4155_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__1;
                v___f_4156_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_4148_);
                v___f_4157_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4157_, 0, v_toFunctor_4148_);
                v___f_4158_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4158_, 0, v_toFunctor_4148_);
                v___x_4159_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4159_, 0, v___f_4157_);
                crate::leanh::lean_ctor_set(v___x_4159_, 1, v___f_4158_);
                v___f_4160_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4160_, 0, v_toSeqRight_4151_);
                v___f_4161_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4161_, 0, v_toSeqLeft_4150_);
                v___f_4162_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4162_, 0, v_toSeq_4149_);
                if v_isShared_4154_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4153_, 4, v___f_4160_);
                    crate::leanh::lean_ctor_set(v___x_4153_, 3, v___f_4161_);
                    crate::leanh::lean_ctor_set(v___x_4153_, 2, v___f_4162_);
                    crate::leanh::lean_ctor_set(v___x_4153_, 1, v___f_4155_);
                    crate::leanh::lean_ctor_set(v___x_4153_, 0, v___x_4159_);
                    v___x_4164_ = v___x_4153_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4232_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4232_, 0, v___x_4159_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4232_, 1, v___f_4155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4232_, 2, v___f_4162_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4232_, 3, v___f_4161_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4232_, 4, v___f_4160_);
                    v___x_4164_ = v_reuseFailAlloc_4232_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4147_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4146_, 1, v___f_4156_);
                    crate::leanh::lean_ctor_set(v___x_4146_, 0, v___x_4164_);
                    v___x_4166_ = v___x_4146_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4231_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 0, v___x_4164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 1, v___f_4156_);
                    v___x_4166_ = v_reuseFailAlloc_4231_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4167_ = l_StateRefT_x27_instMonad___redArg(v___x_4166_);
                v_toApplicative_4168_ = crate::leanh::lean_ctor_get(v___x_4167_, 0);
                v_isSharedCheck_4229_ = (!crate::leanh::lean_is_exclusive(v___x_4167_)) as u8;
                if v_isSharedCheck_4229_ == 0 {
                    v_unused_4230_ = crate::leanh::lean_ctor_get(v___x_4167_, 1);
                    crate::leanh::lean_dec(v_unused_4230_);
                    v___x_4170_ = v___x_4167_;
                    v_isShared_4171_ = v_isSharedCheck_4229_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_4168_);
                    crate::leanh::lean_dec(v___x_4167_);
                    v___x_4170_ = crate::leanh::lean_box(0);
                    v_isShared_4171_ = v_isSharedCheck_4229_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_4172_ = crate::leanh::lean_ctor_get(v_toApplicative_4168_, 0);
                v_toSeq_4173_ = crate::leanh::lean_ctor_get(v_toApplicative_4168_, 2);
                v_toSeqLeft_4174_ = crate::leanh::lean_ctor_get(v_toApplicative_4168_, 3);
                v_toSeqRight_4175_ = crate::leanh::lean_ctor_get(v_toApplicative_4168_, 4);
                v_isSharedCheck_4227_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_4168_)) as u8;
                if v_isSharedCheck_4227_ == 0 {
                    v_unused_4228_ = crate::leanh::lean_ctor_get(v_toApplicative_4168_, 1);
                    crate::leanh::lean_dec(v_unused_4228_);
                    v___x_4177_ = v_toApplicative_4168_;
                    v_isShared_4178_ = v_isSharedCheck_4227_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_4175_);
                    crate::leanh::lean_inc(v_toSeqLeft_4174_);
                    crate::leanh::lean_inc(v_toSeq_4173_);
                    crate::leanh::lean_inc(v_toFunctor_4172_);
                    crate::leanh::lean_dec(v_toApplicative_4168_);
                    v___x_4177_ = crate::leanh::lean_box(0);
                    v_isShared_4178_ = v_isSharedCheck_4227_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_4179_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__3;
                v___f_4180_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_4172_);
                v___f_4181_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4181_, 0, v_toFunctor_4172_);
                v___f_4182_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4182_, 0, v_toFunctor_4172_);
                v___x_4183_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4183_, 0, v___f_4181_);
                crate::leanh::lean_ctor_set(v___x_4183_, 1, v___f_4182_);
                v___f_4184_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4184_, 0, v_toSeqRight_4175_);
                v___f_4185_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4185_, 0, v_toSeqLeft_4174_);
                v___f_4186_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4186_, 0, v_toSeq_4173_);
                if v_isShared_4178_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4177_, 4, v___f_4184_);
                    crate::leanh::lean_ctor_set(v___x_4177_, 3, v___f_4185_);
                    crate::leanh::lean_ctor_set(v___x_4177_, 2, v___f_4186_);
                    crate::leanh::lean_ctor_set(v___x_4177_, 1, v___f_4179_);
                    crate::leanh::lean_ctor_set(v___x_4177_, 0, v___x_4183_);
                    v___x_4188_ = v___x_4177_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4226_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4183_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 1, v___f_4179_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 2, v___f_4186_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 3, v___f_4185_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 4, v___f_4184_);
                    v___x_4188_ = v_reuseFailAlloc_4226_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4171_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4170_, 1, v___f_4180_);
                    crate::leanh::lean_ctor_set(v___x_4170_, 0, v___x_4188_);
                    v___x_4190_ = v___x_4170_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4225_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4188_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 1, v___f_4180_);
                    v___x_4190_ = v_reuseFailAlloc_4225_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4191_ = l_StateRefT_x27_instMonad___redArg(v___x_4190_);
                v_toApplicative_4192_ = crate::leanh::lean_ctor_get(v___x_4191_, 0);
                v_isSharedCheck_4223_ = (!crate::leanh::lean_is_exclusive(v___x_4191_)) as u8;
                if v_isSharedCheck_4223_ == 0 {
                    v_unused_4224_ = crate::leanh::lean_ctor_get(v___x_4191_, 1);
                    crate::leanh::lean_dec(v_unused_4224_);
                    v___x_4194_ = v___x_4191_;
                    v_isShared_4195_ = v_isSharedCheck_4223_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_4192_);
                    crate::leanh::lean_dec(v___x_4191_);
                    v___x_4194_ = crate::leanh::lean_box(0);
                    v_isShared_4195_ = v_isSharedCheck_4223_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_toFunctor_4196_ = crate::leanh::lean_ctor_get(v_toApplicative_4192_, 0);
                v_toSeq_4197_ = crate::leanh::lean_ctor_get(v_toApplicative_4192_, 2);
                v_toSeqLeft_4198_ = crate::leanh::lean_ctor_get(v_toApplicative_4192_, 3);
                v_toSeqRight_4199_ = crate::leanh::lean_ctor_get(v_toApplicative_4192_, 4);
                v_isSharedCheck_4221_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_4192_)) as u8;
                if v_isSharedCheck_4221_ == 0 {
                    v_unused_4222_ = crate::leanh::lean_ctor_get(v_toApplicative_4192_, 1);
                    crate::leanh::lean_dec(v_unused_4222_);
                    v___x_4201_ = v_toApplicative_4192_;
                    v_isShared_4202_ = v_isSharedCheck_4221_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_4199_);
                    crate::leanh::lean_inc(v_toSeqLeft_4198_);
                    crate::leanh::lean_inc(v_toSeq_4197_);
                    crate::leanh::lean_inc(v_toFunctor_4196_);
                    crate::leanh::lean_dec(v_toApplicative_4192_);
                    v___x_4201_ = crate::leanh::lean_box(0);
                    v_isShared_4202_ = v_isSharedCheck_4221_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___f_4203_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__5;
                v___f_4204_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__6;
                crate::leanh::lean_inc_ref(v_toFunctor_4196_);
                v___f_4205_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4205_, 0, v_toFunctor_4196_);
                v___f_4206_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4206_, 0, v_toFunctor_4196_);
                v___x_4207_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4207_, 0, v___f_4205_);
                crate::leanh::lean_ctor_set(v___x_4207_, 1, v___f_4206_);
                v___f_4208_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4208_, 0, v_toSeqRight_4199_);
                v___f_4209_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4209_, 0, v_toSeqLeft_4198_);
                v___f_4210_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4210_, 0, v_toSeq_4197_);
                if v_isShared_4202_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4201_, 4, v___f_4208_);
                    crate::leanh::lean_ctor_set(v___x_4201_, 3, v___f_4209_);
                    crate::leanh::lean_ctor_set(v___x_4201_, 2, v___f_4210_);
                    crate::leanh::lean_ctor_set(v___x_4201_, 1, v___f_4203_);
                    crate::leanh::lean_ctor_set(v___x_4201_, 0, v___x_4207_);
                    v___x_4212_ = v___x_4201_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4220_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4207_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 1, v___f_4203_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 2, v___f_4210_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 3, v___f_4209_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 4, v___f_4208_);
                    v___x_4212_ = v_reuseFailAlloc_4220_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4195_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4194_, 1, v___f_4204_);
                    crate::leanh::lean_ctor_set(v___x_4194_, 0, v___x_4212_);
                    v___x_4214_ = v___x_4194_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4219_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 1, v___f_4204_);
                    v___x_4214_ = v_reuseFailAlloc_4219_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_4215_ = crate::leanh::lean_box(0);
                v___x_4216_ = l_instInhabitedOfMonad___redArg(v___x_4214_, v___x_4215_);
                v___x_19815__overap_4217_ = lean_panic_fn_borrowed(v___x_4216_, v_msg_4134_);
                crate::leanh::lean_dec(v___x_4216_);
                crate::leanh::lean_inc(v___y_4140_);
                crate::leanh::lean_inc_ref(v___y_4139_);
                crate::leanh::lean_inc(v___y_4138_);
                crate::leanh::lean_inc_ref(v___y_4137_);
                crate::leanh::lean_inc(v___y_4136_);
                crate::leanh::lean_inc_ref(v___y_4135_);
                v___x_4218_ = crate::leanh::lean_apply_7(
                    v___x_19815__overap_4217_,
                    v___y_4135_,
                    v___y_4136_,
                    v___y_4137_,
                    v___y_4138_,
                    v___y_4139_,
                    v___y_4140_,
                    crate::leanh::lean_box(0),
                );
                return v___x_4218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___boxed(
    mut v_msg_4237_: *mut crate::leanh::LeanObject,
    mut v___y_4238_: *mut crate::leanh::LeanObject,
    mut v___y_4239_: *mut crate::leanh::LeanObject,
    mut v___y_4240_: *mut crate::leanh::LeanObject,
    mut v___y_4241_: *mut crate::leanh::LeanObject,
    mut v___y_4242_: *mut crate::leanh::LeanObject,
    mut v___y_4243_: *mut crate::leanh::LeanObject,
    mut v___y_4244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4245_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0(v_msg_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
    crate::leanh::lean_dec(v___y_4243_);
    crate::leanh::lean_dec_ref(v___y_4242_);
    crate::leanh::lean_dec(v___y_4241_);
    crate::leanh::lean_dec_ref(v___y_4240_);
    crate::leanh::lean_dec(v___y_4239_);
    crate::leanh::lean_dec_ref(v___y_4238_);
    return v_res_4245_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4247_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__0;
    v___x_4248_ = l_Lean_stringToMessageData(v___x_4247_);
    return v___x_4248_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4250_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__2;
    v___x_4251_ = l_Lean_stringToMessageData(v___x_4250_);
    return v___x_4251_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4255_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__6;
    v___x_4256_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_4257_ = crate::leanh::lean_unsigned_to_nat(122);
    v___x_4258_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__5;
    v___x_4259_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__4;
    v___x_4260_ = l_mkPanicMessageWithDecl(
        v___x_4259_,
        v___x_4258_,
        v___x_4257_,
        v___x_4256_,
        v___x_4255_,
    );
    return v___x_4260_;
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(
    mut v_constName_4261_: *mut crate::leanh::LeanObject,
    mut v___y_4262_: *mut crate::leanh::LeanObject,
    mut v___y_4263_: *mut crate::leanh::LeanObject,
    mut v___y_4264_: *mut crate::leanh::LeanObject,
    mut v___y_4265_: *mut crate::leanh::LeanObject,
    mut v___y_4266_: *mut crate::leanh::LeanObject,
    mut v___y_4267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: u8 = 0;
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: u8 = 0;
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_4282_: u8 = 0;
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4287_: u8 = 0;
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4291_: u8 = 0;
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4297_: u8 = 0;
    let mut v_val_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4302_: u8 = 0;
    let mut v_a_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4306_: u8 = 0;
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4277_ = lean_st_ref_get(v___y_4267_);
                v_env_4278_ = crate::leanh::lean_ctor_get(v___x_4277_, 0);
                crate::leanh::lean_inc_ref(v_env_4278_);
                crate::leanh::lean_dec(v___x_4277_);
                v___x_4279_ = 0;
                crate::leanh::lean_inc(v_constName_4261_);
                v___x_4280_ =
                    l_Lean_Environment_findAsync_x3f(v_env_4278_, v_constName_4261_, v___x_4279_);
                if crate::leanh::lean_obj_tag(v___x_4280_) == 1 {
                    v_val_4281_ = crate::leanh::lean_ctor_get(v___x_4280_, 0);
                    crate::leanh::lean_inc(v_val_4281_);
                    crate::leanh::lean_dec_ref_known(v___x_4280_, 1);
                    v_kind_4282_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_4281_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    if v_kind_4282_ == 6 {
                        v___x_4283_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4281_);
                        if crate::leanh::lean_obj_tag(v___x_4283_) == 6 {
                            crate::leanh::lean_dec(v_constName_4261_);
                            v_val_4284_ = crate::leanh::lean_ctor_get(v___x_4283_, 0);
                            v_isSharedCheck_4291_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4283_)) as u8;
                            if v_isSharedCheck_4291_ == 0 {
                                v___x_4286_ = v___x_4283_;
                                v_isShared_4287_ = v_isSharedCheck_4291_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_4284_);
                                crate::leanh::lean_dec(v___x_4283_);
                                v___x_4286_ = crate::leanh::lean_box(0);
                                v_isShared_4287_ = v_isSharedCheck_4291_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4283_);
                            v___x_4292_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7);
                            v___x_4293_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0(v___x_4292_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
                            if crate::leanh::lean_obj_tag(v___x_4293_) == 0 {
                                v_a_4294_ = crate::leanh::lean_ctor_get(v___x_4293_, 0);
                                v_isSharedCheck_4302_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4293_)) as u8;
                                if v_isSharedCheck_4302_ == 0 {
                                    v___x_4296_ = v___x_4293_;
                                    v_isShared_4297_ = v_isSharedCheck_4302_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4294_);
                                    crate::leanh::lean_dec(v___x_4293_);
                                    v___x_4296_ = crate::leanh::lean_box(0);
                                    v_isShared_4297_ = v_isSharedCheck_4302_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_constName_4261_);
                                v_a_4303_ = crate::leanh::lean_ctor_get(v___x_4293_, 0);
                                v_isSharedCheck_4310_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4293_)) as u8;
                                if v_isSharedCheck_4310_ == 0 {
                                    v___x_4305_ = v___x_4293_;
                                    v_isShared_4306_ = v_isSharedCheck_4310_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4303_);
                                    crate::leanh::lean_dec(v___x_4293_);
                                    v___x_4305_ = crate::leanh::lean_box(0);
                                    v_isShared_4306_ = v_isSharedCheck_4310_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4281_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4280_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4270_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1);
                v___x_4271_ = 0;
                v___x_4272_ = l_Lean_MessageData_ofConstName(v_constName_4261_, v___x_4271_);
                v___x_4273_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4273_, 0, v___x_4270_);
                crate::leanh::lean_ctor_set(v___x_4273_, 1, v___x_4272_);
                v___x_4274_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3);
                v___x_4275_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4275_, 0, v___x_4273_);
                crate::leanh::lean_ctor_set(v___x_4275_, 1, v___x_4274_);
                v___x_4276_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(v___x_4275_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
                return v___x_4276_;
            }
            2 => {
                if v_isShared_4287_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4286_, 0);
                    v___x_4289_ = v___x_4286_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4290_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_val_4284_);
                    v___x_4289_ = v_reuseFailAlloc_4290_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4289_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_4294_) == 0 {
                    crate::leanh::lean_del_object(v___x_4296_);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_constName_4261_);
                    v_val_4298_ = crate::leanh::lean_ctor_get(v_a_4294_, 0);
                    crate::leanh::lean_inc(v_val_4298_);
                    crate::leanh::lean_dec_ref_known(v_a_4294_, 1);
                    if v_isShared_4297_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4296_, 0, v_val_4298_);
                        v___x_4300_ = v___x_4296_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4301_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_val_4298_);
                        v___x_4300_ = v_reuseFailAlloc_4301_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_4300_;
            }
            6 => {
                if v_isShared_4306_ == 0 {
                    v___x_4308_ = v___x_4305_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4309_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4303_);
                    v___x_4308_ = v_reuseFailAlloc_4309_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___boxed(
    mut v_constName_4311_: *mut crate::leanh::LeanObject,
    mut v___y_4312_: *mut crate::leanh::LeanObject,
    mut v___y_4313_: *mut crate::leanh::LeanObject,
    mut v___y_4314_: *mut crate::leanh::LeanObject,
    mut v___y_4315_: *mut crate::leanh::LeanObject,
    mut v___y_4316_: *mut crate::leanh::LeanObject,
    mut v___y_4317_: *mut crate::leanh::LeanObject,
    mut v___y_4318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4319_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(
        v_constName_4311_,
        v___y_4312_,
        v___y_4313_,
        v___y_4314_,
        v___y_4315_,
        v___y_4316_,
        v___y_4317_,
    );
    crate::leanh::lean_dec(v___y_4317_);
    crate::leanh::lean_dec_ref(v___y_4316_);
    crate::leanh::lean_dec(v___y_4315_);
    crate::leanh::lean_dec_ref(v___y_4314_);
    crate::leanh::lean_dec(v___y_4313_);
    crate::leanh::lean_dec_ref(v___y_4312_);
    return v_res_4319_;
}
pub unsafe fn l_Lean_Elab_Deriving_Repr_mkBodyForStruct(
    mut v_header_4320_: *mut crate::leanh::LeanObject,
    mut v_indVal_4321_: *mut crate::leanh::LeanObject,
    mut v_a_4322_: *mut crate::leanh::LeanObject,
    mut v_a_4323_: *mut crate::leanh::LeanObject,
    mut v_a_4324_: *mut crate::leanh::LeanObject,
    mut v_a_4325_: *mut crate::leanh::LeanObject,
    mut v_a_4326_: *mut crate::leanh::LeanObject,
    mut v_a_4327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toConstantVal_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_targetNames_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: u8 = 0;
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4352_: u8 = 0;
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4356_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toConstantVal_4329_ = crate::leanh::lean_ctor_get(v_indVal_4321_, 0);
                crate::leanh::lean_inc_ref(v_toConstantVal_4329_);
                v_numParams_4330_ = crate::leanh::lean_ctor_get(v_indVal_4321_, 1);
                crate::leanh::lean_inc(v_numParams_4330_);
                v_ctors_4331_ = crate::leanh::lean_ctor_get(v_indVal_4321_, 4);
                crate::leanh::lean_inc(v_ctors_4331_);
                crate::leanh::lean_dec_ref(v_indVal_4321_);
                v___x_4332_ = crate::leanh::lean_box(0);
                v___x_4333_ = l_List_head_x21___redArg(v___x_4332_, v_ctors_4331_);
                crate::leanh::lean_dec(v_ctors_4331_);
                v___x_4334_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(v___x_4333_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_);
                if crate::leanh::lean_obj_tag(v___x_4334_) == 0 {
                    v_a_4335_ = crate::leanh::lean_ctor_get(v___x_4334_, 0);
                    crate::leanh::lean_inc(v_a_4335_);
                    crate::leanh::lean_dec_ref_known(v___x_4334_, 1);
                    v___x_4336_ = lean_st_ref_get(v_a_4327_);
                    v_toConstantVal_4337_ = crate::leanh::lean_ctor_get(v_a_4335_, 0);
                    crate::leanh::lean_inc_ref(v_toConstantVal_4337_);
                    crate::leanh::lean_dec(v_a_4335_);
                    v_env_4338_ = crate::leanh::lean_ctor_get(v___x_4336_, 0);
                    crate::leanh::lean_inc_ref(v_env_4338_);
                    crate::leanh::lean_dec(v___x_4336_);
                    v_name_4339_ = crate::leanh::lean_ctor_get(v_toConstantVal_4329_, 0);
                    crate::leanh::lean_inc(v_name_4339_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_4329_);
                    v_targetNames_4340_ = crate::leanh::lean_ctor_get(v_header_4320_, 2);
                    v_type_4341_ = crate::leanh::lean_ctor_get(v_toConstantVal_4337_, 2);
                    crate::leanh::lean_inc_ref(v_type_4341_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_4337_);
                    v___x_4342_ = l_Lean_getStructureFields(v_env_4338_, v_name_4339_);
                    v___x_4343_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4344_ =
                        lean_array_get_borrowed(v___x_4332_, v_targetNames_4340_, v___x_4343_);
                    crate::leanh::lean_inc(v___x_4344_);
                    v___x_4345_ = lean_mk_syntax_ident(v___x_4344_);
                    v___f_4346_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___boxed
                            as *mut core::ffi::c_void,
                        13,
                        4,
                    );
                    crate::leanh::lean_closure_set(v___f_4346_, 0, v___x_4342_);
                    crate::leanh::lean_closure_set(v___f_4346_, 1, v_numParams_4330_);
                    crate::leanh::lean_closure_set(v___f_4346_, 2, v___x_4345_);
                    crate::leanh::lean_closure_set(v___f_4346_, 3, v___x_4343_);
                    v___x_4347_ = 0;
                    v___x_4348_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(v_type_4341_, v___f_4346_, v___x_4347_, v___x_4347_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_);
                    return v___x_4348_;
                } else {
                    crate::leanh::lean_dec(v_numParams_4330_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_4329_);
                    v_a_4349_ = crate::leanh::lean_ctor_get(v___x_4334_, 0);
                    v_isSharedCheck_4356_ = (!crate::leanh::lean_is_exclusive(v___x_4334_)) as u8;
                    if v_isSharedCheck_4356_ == 0 {
                        v___x_4351_ = v___x_4334_;
                        v_isShared_4352_ = v_isSharedCheck_4356_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4349_);
                        crate::leanh::lean_dec(v___x_4334_);
                        v___x_4351_ = crate::leanh::lean_box(0);
                        v_isShared_4352_ = v_isSharedCheck_4356_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4352_ == 0 {
                    v___x_4354_ = v___x_4351_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4355_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_a_4349_);
                    v___x_4354_ = v_reuseFailAlloc_4355_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4354_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_Repr_mkBodyForStruct___boxed(
    mut v_header_4357_: *mut crate::leanh::LeanObject,
    mut v_indVal_4358_: *mut crate::leanh::LeanObject,
    mut v_a_4359_: *mut crate::leanh::LeanObject,
    mut v_a_4360_: *mut crate::leanh::LeanObject,
    mut v_a_4361_: *mut crate::leanh::LeanObject,
    mut v_a_4362_: *mut crate::leanh::LeanObject,
    mut v_a_4363_: *mut crate::leanh::LeanObject,
    mut v_a_4364_: *mut crate::leanh::LeanObject,
    mut v_a_4365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4366_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct(
        v_header_4357_,
        v_indVal_4358_,
        v_a_4359_,
        v_a_4360_,
        v_a_4361_,
        v_a_4362_,
        v_a_4363_,
        v_a_4364_,
    );
    crate::leanh::lean_dec(v_a_4364_);
    crate::leanh::lean_dec_ref(v_a_4363_);
    crate::leanh::lean_dec(v_a_4362_);
    crate::leanh::lean_dec_ref(v_a_4361_);
    crate::leanh::lean_dec(v_a_4360_);
    crate::leanh::lean_dec_ref(v_a_4359_);
    crate::leanh::lean_dec_ref(v_header_4357_);
    return v_res_4366_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1(
    mut v___x_4367_: *mut crate::leanh::LeanObject,
    mut v___x_4368_: *mut crate::leanh::LeanObject,
    mut v_inst_4369_: *mut crate::leanh::LeanObject,
    mut v_R_4370_: *mut crate::leanh::LeanObject,
    mut v_a_4371_: *mut crate::leanh::LeanObject,
    mut v_b_4372_: *mut crate::leanh::LeanObject,
    mut v_c_4373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4374_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(v___x_4367_, v___x_4368_, v_a_4371_, v_b_4372_);
    return v___x_4374_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___boxed(
    mut v___x_4375_: *mut crate::leanh::LeanObject,
    mut v___x_4376_: *mut crate::leanh::LeanObject,
    mut v_inst_4377_: *mut crate::leanh::LeanObject,
    mut v_R_4378_: *mut crate::leanh::LeanObject,
    mut v_a_4379_: *mut crate::leanh::LeanObject,
    mut v_b_4380_: *mut crate::leanh::LeanObject,
    mut v_c_4381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4382_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1(
            v___x_4375_,
            v___x_4376_,
            v_inst_4377_,
            v_R_4378_,
            v_a_4379_,
            v_b_4380_,
            v_c_4381_,
        );
    crate::leanh::lean_dec_ref(v___x_4376_);
    crate::leanh::lean_dec_ref(v___x_4375_);
    return v_res_4382_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2(
    mut v_upperBound_4383_: *mut crate::leanh::LeanObject,
    mut v___x_4384_: *mut crate::leanh::LeanObject,
    mut v___x_4385_: *mut crate::leanh::LeanObject,
    mut v_xs_4386_: *mut crate::leanh::LeanObject,
    mut v___x_4387_: *mut crate::leanh::LeanObject,
    mut v_inst_4388_: *mut crate::leanh::LeanObject,
    mut v_R_4389_: *mut crate::leanh::LeanObject,
    mut v_a_4390_: *mut crate::leanh::LeanObject,
    mut v_b_4391_: *mut crate::leanh::LeanObject,
    mut v_c_4392_: *mut crate::leanh::LeanObject,
    mut v___y_4393_: *mut crate::leanh::LeanObject,
    mut v___y_4394_: *mut crate::leanh::LeanObject,
    mut v___y_4395_: *mut crate::leanh::LeanObject,
    mut v___y_4396_: *mut crate::leanh::LeanObject,
    mut v___y_4397_: *mut crate::leanh::LeanObject,
    mut v___y_4398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4400_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(v_upperBound_4383_, v___x_4384_, v___x_4385_, v_xs_4386_, v___x_4387_, v_a_4390_, v_b_4391_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_);
    return v___x_4400_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_4401_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_4402_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_4403_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_xs_4404_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_4405_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_4406_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_R_4407_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_4408_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_b_4409_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_c_4410_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4411_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4412_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4413_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4414_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4415_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4416_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4417_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4418_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2(
            v_upperBound_4401_,
            v___x_4402_,
            v___x_4403_,
            v_xs_4404_,
            v___x_4405_,
            v_inst_4406_,
            v_R_4407_,
            v_a_4408_,
            v_b_4409_,
            v_c_4410_,
            v___y_4411_,
            v___y_4412_,
            v___y_4413_,
            v___y_4414_,
            v___y_4415_,
            v___y_4416_,
        );
    crate::leanh::lean_dec(v___y_4416_);
    crate::leanh::lean_dec_ref(v___y_4415_);
    crate::leanh::lean_dec(v___y_4414_);
    crate::leanh::lean_dec_ref(v___y_4413_);
    crate::leanh::lean_dec(v___y_4412_);
    crate::leanh::lean_dec_ref(v___y_4411_);
    crate::leanh::lean_dec_ref(v_xs_4404_);
    crate::leanh::lean_dec(v___x_4403_);
    crate::leanh::lean_dec_ref(v___x_4402_);
    crate::leanh::lean_dec(v_upperBound_4401_);
    return v_res_4418_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3(
    mut v_00_u03b1_4419_: *mut crate::leanh::LeanObject,
    mut v_msg_4420_: *mut crate::leanh::LeanObject,
    mut v___y_4421_: *mut crate::leanh::LeanObject,
    mut v___y_4422_: *mut crate::leanh::LeanObject,
    mut v___y_4423_: *mut crate::leanh::LeanObject,
    mut v___y_4424_: *mut crate::leanh::LeanObject,
    mut v___y_4425_: *mut crate::leanh::LeanObject,
    mut v___y_4426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4428_ =
        l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(
            v_msg_4420_,
            v___y_4421_,
            v___y_4422_,
            v___y_4423_,
            v___y_4424_,
            v___y_4425_,
            v___y_4426_,
        );
    return v___x_4428_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___boxed(
    mut v_00_u03b1_4429_: *mut crate::leanh::LeanObject,
    mut v_msg_4430_: *mut crate::leanh::LeanObject,
    mut v___y_4431_: *mut crate::leanh::LeanObject,
    mut v___y_4432_: *mut crate::leanh::LeanObject,
    mut v___y_4433_: *mut crate::leanh::LeanObject,
    mut v___y_4434_: *mut crate::leanh::LeanObject,
    mut v___y_4435_: *mut crate::leanh::LeanObject,
    mut v___y_4436_: *mut crate::leanh::LeanObject,
    mut v___y_4437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4438_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3(
        v_00_u03b1_4429_,
        v_msg_4430_,
        v___y_4431_,
        v___y_4432_,
        v___y_4433_,
        v___y_4434_,
        v___y_4435_,
        v___y_4436_,
    );
    crate::leanh::lean_dec(v___y_4436_);
    crate::leanh::lean_dec_ref(v___y_4435_);
    crate::leanh::lean_dec(v___y_4434_);
    crate::leanh::lean_dec_ref(v___y_4433_);
    crate::leanh::lean_dec(v___y_4432_);
    crate::leanh::lean_dec_ref(v___y_4431_);
    return v_res_4438_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5(
    mut v_msgData_4439_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4440_: *mut crate::leanh::LeanObject,
    mut v___y_4441_: *mut crate::leanh::LeanObject,
    mut v___y_4442_: *mut crate::leanh::LeanObject,
    mut v___y_4443_: *mut crate::leanh::LeanObject,
    mut v___y_4444_: *mut crate::leanh::LeanObject,
    mut v___y_4445_: *mut crate::leanh::LeanObject,
    mut v___y_4446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4448_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg(v_msgData_4439_, v_macroStack_4440_, v___y_4445_);
    return v___x_4448_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___boxed(
    mut v_msgData_4449_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4450_: *mut crate::leanh::LeanObject,
    mut v___y_4451_: *mut crate::leanh::LeanObject,
    mut v___y_4452_: *mut crate::leanh::LeanObject,
    mut v___y_4453_: *mut crate::leanh::LeanObject,
    mut v___y_4454_: *mut crate::leanh::LeanObject,
    mut v___y_4455_: *mut crate::leanh::LeanObject,
    mut v___y_4456_: *mut crate::leanh::LeanObject,
    mut v___y_4457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4458_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5(v_msgData_4449_, v_macroStack_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
    crate::leanh::lean_dec(v___y_4456_);
    crate::leanh::lean_dec_ref(v___y_4455_);
    crate::leanh::lean_dec(v___y_4454_);
    crate::leanh::lean_dec_ref(v___y_4453_);
    crate::leanh::lean_dec(v___y_4452_);
    crate::leanh::lean_dec_ref(v___y_4451_);
    return v_res_4458_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(
    mut v_upperBound_4466_: *mut crate::leanh::LeanObject,
    mut v_a_4467_: *mut crate::leanh::LeanObject,
    mut v_b_4468_: *mut crate::leanh::LeanObject,
    mut v___y_4469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4471_: u8 = 0;
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: u8 = 0;
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4471_ = lean_nat_dec_lt(v_a_4467_, v_upperBound_4466_);
                if v___x_4471_ == 0 {
                    crate::leanh::lean_dec(v_a_4467_);
                    v___x_4472_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4472_, 0, v_b_4468_);
                    return v___x_4472_;
                } else {
                    v_ref_4473_ = crate::leanh::lean_ctor_get(v___y_4469_, 5);
                    v___x_4474_ = 0;
                    v___x_4475_ = l_Lean_SourceInfo_fromRef(v_ref_4473_, v___x_4474_);
                    v___x_4476_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1;
                    v___x_4477_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2;
                    crate::leanh::lean_inc(v___x_4475_);
                    v___x_4478_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4478_, 0, v___x_4475_);
                    crate::leanh::lean_ctor_set(v___x_4478_, 1, v___x_4477_);
                    v___x_4479_ = l_Lean_Syntax_node1(v___x_4475_, v___x_4476_, v___x_4478_);
                    v___x_4480_ = lean_array_push(v_b_4468_, v___x_4479_);
                    v___x_4481_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4482_ = lean_nat_add(v_a_4467_, v___x_4481_);
                    crate::leanh::lean_dec(v_a_4467_);
                    v_a_4467_ = v___x_4482_;
                    v_b_4468_ = v___x_4480_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___boxed(
    mut v_upperBound_4484_: *mut crate::leanh::LeanObject,
    mut v_a_4485_: *mut crate::leanh::LeanObject,
    mut v_b_4486_: *mut crate::leanh::LeanObject,
    mut v___y_4487_: *mut crate::leanh::LeanObject,
    mut v___y_4488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4489_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(v_upperBound_4484_, v_a_4485_, v_b_4486_, v___y_4487_);
    crate::leanh::lean_dec_ref(v___y_4487_);
    crate::leanh::lean_dec(v_upperBound_4484_);
    return v_res_4489_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(
    mut v_sz_4490_: usize,
    mut v_i_4491_: usize,
    mut v_bs_4492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4493_: u8 = 0;
    let mut v_v_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: usize = 0;
    let mut v___x_4498_: usize = 0;
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4493_ = lean_usize_dec_lt(v_i_4491_, v_sz_4490_);
                if v___x_4493_ == 0 {
                    return v_bs_4492_;
                } else {
                    v_v_4494_ = lean_array_uget(v_bs_4492_, v_i_4491_);
                    v___x_4495_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4496_ = lean_array_uset(v_bs_4492_, v_i_4491_, v___x_4495_);
                    v___x_4497_ = 1usize;
                    v___x_4498_ = lean_usize_add(v_i_4491_, v___x_4497_);
                    v___x_4499_ = lean_array_uset(v_bs_x27_4496_, v_i_4491_, v_v_4494_);
                    v_i_4491_ = v___x_4498_;
                    v_bs_4492_ = v___x_4499_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0___boxed(
    mut v_sz_4501_: *mut crate::leanh::LeanObject,
    mut v_i_4502_: *mut crate::leanh::LeanObject,
    mut v_bs_4503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4504_: usize = 0;
    let mut v_i_boxed_4505_: usize = 0;
    let mut v_res_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4504_ = crate::leanh::lean_unbox_usize(v_sz_4501_);
    crate::leanh::lean_dec(v_sz_4501_);
    v_i_boxed_4505_ = crate::leanh::lean_unbox_usize(v_i_4502_);
    crate::leanh::lean_dec(v_i_4502_);
    v_res_4506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(v_sz_boxed_4504_, v_i_boxed_4505_, v_bs_4503_);
    return v_res_4506_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4508_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0;
    v___x_4509_ = l_String_toRawSubstring_x27(v___x_4508_);
    return v___x_4509_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(
    mut v___x_4522_: *mut crate::leanh::LeanObject,
    mut v_snd_4523_: *mut crate::leanh::LeanObject,
    mut v_toConstantVal_4524_: *mut crate::leanh::LeanObject,
    mut v___f_4525_: *mut crate::leanh::LeanObject,
    mut v___x_4526_: *mut crate::leanh::LeanObject,
    mut v_auxFunName_4527_: *mut crate::leanh::LeanObject,
    mut v_____r_4528_: *mut crate::leanh::LeanObject,
    mut v_ctorArgs_4529_: *mut crate::leanh::LeanObject,
    mut v___y_4530_: *mut crate::leanh::LeanObject,
    mut v___y_4531_: *mut crate::leanh::LeanObject,
    mut v___y_4532_: *mut crate::leanh::LeanObject,
    mut v___y_4533_: *mut crate::leanh::LeanObject,
    mut v___y_4534_: *mut crate::leanh::LeanObject,
    mut v___y_4535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: u8 = 0;
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4545_: u8 = 0;
    let mut v_quotContext_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4572_: u8 = 0;
    let mut v_a_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4576_: u8 = 0;
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4580_: u8 = 0;
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4585_: u8 = 0;
    let mut v_quotContext_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4607_: u8 = 0;
    let mut v_a_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4611_: u8 = 0;
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4615_: u8 = 0;
    let mut v_a_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4619_: u8 = 0;
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4623_: u8 = 0;
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4629_: u8 = 0;
    let mut v___x_4630_: u8 = 0;
    let mut v___x_4631_: u8 = 0;
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: u8 = 0;
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: u8 = 0;
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4649_: u8 = 0;
    let mut v_quotContext_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4676_: u8 = 0;
    let mut v_a_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4680_: u8 = 0;
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4684_: u8 = 0;
    let mut v_a_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4688_: u8 = 0;
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4692_: u8 = 0;
    let mut v_isSharedCheck_4693_: u8 = 0;
    let mut v_a_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4697_: u8 = 0;
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4624_ = l_Lean_Expr_fvarId_x21(v___x_4522_);
                v___x_4625_ = l_Lean_FVarId_getBinderInfo___redArg(
                    v___x_4624_,
                    v___y_4532_,
                    v___y_4534_,
                    v___y_4535_,
                );
                if crate::leanh::lean_obj_tag(v___x_4625_) == 0 {
                    v_a_4626_ = crate::leanh::lean_ctor_get(v___x_4625_, 0);
                    v_isSharedCheck_4693_ = (!crate::leanh::lean_is_exclusive(v___x_4625_)) as u8;
                    if v_isSharedCheck_4693_ == 0 {
                        v___x_4628_ = v___x_4625_;
                        v_isShared_4629_ = v_isSharedCheck_4693_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4626_);
                        crate::leanh::lean_dec(v___x_4625_);
                        v___x_4628_ = crate::leanh::lean_box(0);
                        v_isShared_4629_ = v_isSharedCheck_4693_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_ctorArgs_4529_);
                    crate::leanh::lean_dec(v_auxFunName_4527_);
                    crate::leanh::lean_dec(v___x_4526_);
                    crate::leanh::lean_dec_ref(v___f_4525_);
                    crate::leanh::lean_dec(v_snd_4523_);
                    crate::leanh::lean_dec_ref(v___x_4522_);
                    v_a_4694_ = crate::leanh::lean_ctor_get(v___x_4625_, 0);
                    v_isSharedCheck_4701_ = (!crate::leanh::lean_is_exclusive(v___x_4625_)) as u8;
                    if v_isSharedCheck_4701_ == 0 {
                        v___x_4696_ = v___x_4625_;
                        v_isShared_4697_ = v_isSharedCheck_4701_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4694_);
                        crate::leanh::lean_dec(v___x_4625_);
                        v___x_4696_ = crate::leanh::lean_box(0);
                        v_isShared_4697_ = v_isSharedCheck_4701_;
                        state = 20;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_4538_) == 0 {
                    v_a_4539_ = crate::leanh::lean_ctor_get(v___y_4538_, 0);
                    crate::leanh::lean_inc(v_a_4539_);
                    crate::leanh::lean_dec_ref_known(v___y_4538_, 1);
                    v___x_4540_ = (crate::leanh::lean_unbox(v_a_4539_) as u8);
                    crate::leanh::lean_dec(v_a_4539_);
                    if v___x_4540_ == 0 {
                        crate::leanh::lean_inc(v___y_4535_);
                        crate::leanh::lean_inc_ref(v___y_4534_);
                        crate::leanh::lean_inc(v___y_4533_);
                        crate::leanh::lean_inc_ref(v___y_4532_);
                        crate::leanh::lean_inc(v___y_4531_);
                        crate::leanh::lean_inc_ref(v___y_4530_);
                        v___x_4541_ = crate::leanh::lean_apply_7(
                            v___f_4525_,
                            v___y_4530_,
                            v___y_4531_,
                            v___y_4532_,
                            v___y_4533_,
                            v___y_4534_,
                            v___y_4535_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_4541_) == 0 {
                            v_a_4542_ = crate::leanh::lean_ctor_get(v___x_4541_, 0);
                            v_isSharedCheck_4572_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4541_)) as u8;
                            if v_isSharedCheck_4572_ == 0 {
                                v___x_4544_ = v___x_4541_;
                                v_isShared_4545_ = v_isSharedCheck_4572_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4542_);
                                crate::leanh::lean_dec(v___x_4541_);
                                v___x_4544_ = crate::leanh::lean_box(0);
                                v_isShared_4545_ = v_isSharedCheck_4572_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_ctorArgs_4529_);
                            crate::leanh::lean_dec(v___x_4526_);
                            crate::leanh::lean_dec(v_snd_4523_);
                            v_a_4573_ = crate::leanh::lean_ctor_get(v___x_4541_, 0);
                            v_isSharedCheck_4580_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4541_)) as u8;
                            if v_isSharedCheck_4580_ == 0 {
                                v___x_4575_ = v___x_4541_;
                                v_isShared_4576_ = v_isSharedCheck_4580_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4573_);
                                crate::leanh::lean_dec(v___x_4541_);
                                v___x_4575_ = crate::leanh::lean_box(0);
                                v_isShared_4576_ = v_isSharedCheck_4580_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4526_);
                        crate::leanh::lean_inc(v___y_4535_);
                        crate::leanh::lean_inc_ref(v___y_4534_);
                        crate::leanh::lean_inc(v___y_4533_);
                        crate::leanh::lean_inc_ref(v___y_4532_);
                        crate::leanh::lean_inc(v___y_4531_);
                        crate::leanh::lean_inc_ref(v___y_4530_);
                        v___x_4581_ = crate::leanh::lean_apply_7(
                            v___f_4525_,
                            v___y_4530_,
                            v___y_4531_,
                            v___y_4532_,
                            v___y_4533_,
                            v___y_4534_,
                            v___y_4535_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_4581_) == 0 {
                            v_a_4582_ = crate::leanh::lean_ctor_get(v___x_4581_, 0);
                            v_isSharedCheck_4607_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4581_)) as u8;
                            if v_isSharedCheck_4607_ == 0 {
                                v___x_4584_ = v___x_4581_;
                                v_isShared_4585_ = v_isSharedCheck_4607_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4582_);
                                crate::leanh::lean_dec(v___x_4581_);
                                v___x_4584_ = crate::leanh::lean_box(0);
                                v_isShared_4585_ = v_isSharedCheck_4607_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_ctorArgs_4529_);
                            crate::leanh::lean_dec(v_snd_4523_);
                            v_a_4608_ = crate::leanh::lean_ctor_get(v___x_4581_, 0);
                            v_isSharedCheck_4615_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4581_)) as u8;
                            if v_isSharedCheck_4615_ == 0 {
                                v___x_4610_ = v___x_4581_;
                                v_isShared_4611_ = v_isSharedCheck_4615_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4608_);
                                crate::leanh::lean_dec(v___x_4581_);
                                v___x_4610_ = crate::leanh::lean_box(0);
                                v_isShared_4611_ = v_isSharedCheck_4615_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_ctorArgs_4529_);
                    crate::leanh::lean_dec(v___x_4526_);
                    crate::leanh::lean_dec_ref(v___f_4525_);
                    crate::leanh::lean_dec(v_snd_4523_);
                    v_a_4616_ = crate::leanh::lean_ctor_get(v___y_4538_, 0);
                    v_isSharedCheck_4623_ = (!crate::leanh::lean_is_exclusive(v___y_4538_)) as u8;
                    if v_isSharedCheck_4623_ == 0 {
                        v___x_4618_ = v___y_4538_;
                        v_isShared_4619_ = v_isSharedCheck_4623_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4616_);
                        crate::leanh::lean_dec(v___y_4538_);
                        v___x_4618_ = crate::leanh::lean_box(0);
                        v_isShared_4619_ = v_isSharedCheck_4623_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v_quotContext_4546_ = crate::leanh::lean_ctor_get(v___y_4534_, 10);
                v_currMacroScope_4547_ = crate::leanh::lean_ctor_get(v___y_4534_, 11);
                v___x_4548_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3;
                v___x_4549_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4;
                crate::leanh::lean_inc_n(v_a_4542_, 6);
                v___x_4550_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4550_, 0, v_a_4542_);
                crate::leanh::lean_ctor_set(v___x_4550_, 1, v___x_4549_);
                v___x_4551_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3);
                v___x_4552_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5;
                crate::leanh::lean_inc_n(v_currMacroScope_4547_, 2);
                crate::leanh::lean_inc_n(v_quotContext_4546_, 2);
                v___x_4553_ =
                    l_Lean_addMacroScope(v_quotContext_4546_, v___x_4552_, v_currMacroScope_4547_);
                v___x_4554_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10;
                v___x_4555_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4555_, 0, v_a_4542_);
                crate::leanh::lean_ctor_set(v___x_4555_, 1, v___x_4551_);
                crate::leanh::lean_ctor_set(v___x_4555_, 2, v___x_4553_);
                crate::leanh::lean_ctor_set(v___x_4555_, 3, v___x_4554_);
                crate::leanh::lean_inc_ref(v___x_4550_);
                v___x_4556_ = l_Lean_Syntax_node3(
                    v_a_4542_,
                    v___x_4548_,
                    v_snd_4523_,
                    v___x_4550_,
                    v___x_4555_,
                );
                v___x_4557_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33;
                v___x_4558_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1);
                v___x_4559_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2;
                v___x_4560_ =
                    l_Lean_addMacroScope(v_quotContext_4546_, v___x_4559_, v_currMacroScope_4547_);
                v___x_4561_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__4;
                v___x_4562_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4562_, 0, v_a_4542_);
                crate::leanh::lean_ctor_set(v___x_4562_, 1, v___x_4558_);
                crate::leanh::lean_ctor_set(v___x_4562_, 2, v___x_4560_);
                crate::leanh::lean_ctor_set(v___x_4562_, 3, v___x_4561_);
                v___x_4563_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9;
                v___x_4564_ = l_Lean_Syntax_node1(v_a_4542_, v___x_4563_, v___x_4526_);
                v___x_4565_ = l_Lean_Syntax_node2(v_a_4542_, v___x_4557_, v___x_4562_, v___x_4564_);
                v___x_4566_ = l_Lean_Syntax_node3(
                    v_a_4542_,
                    v___x_4548_,
                    v___x_4556_,
                    v___x_4550_,
                    v___x_4565_,
                );
                v___x_4567_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4567_, 0, v_ctorArgs_4529_);
                crate::leanh::lean_ctor_set(v___x_4567_, 1, v___x_4566_);
                v___x_4568_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4568_, 0, v___x_4567_);
                if v_isShared_4545_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4544_, 0, v___x_4568_);
                    v___x_4570_ = v___x_4544_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4571_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 0, v___x_4568_);
                    v___x_4570_ = v_reuseFailAlloc_4571_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4570_;
            }
            4 => {
                if v_isShared_4576_ == 0 {
                    v___x_4578_ = v___x_4575_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4579_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4579_, 0, v_a_4573_);
                    v___x_4578_ = v_reuseFailAlloc_4579_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4578_;
            }
            6 => {
                v_quotContext_4586_ = crate::leanh::lean_ctor_get(v___y_4534_, 10);
                v_currMacroScope_4587_ = crate::leanh::lean_ctor_get(v___y_4534_, 11);
                v___x_4588_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3;
                v___x_4589_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4;
                crate::leanh::lean_inc_n(v_a_4582_, 5);
                v___x_4590_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4590_, 0, v_a_4582_);
                crate::leanh::lean_ctor_set(v___x_4590_, 1, v___x_4589_);
                v___x_4591_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3);
                v___x_4592_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5;
                crate::leanh::lean_inc(v_currMacroScope_4587_);
                crate::leanh::lean_inc(v_quotContext_4586_);
                v___x_4593_ =
                    l_Lean_addMacroScope(v_quotContext_4586_, v___x_4592_, v_currMacroScope_4587_);
                v___x_4594_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10;
                v___x_4595_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4595_, 0, v_a_4582_);
                crate::leanh::lean_ctor_set(v___x_4595_, 1, v___x_4591_);
                crate::leanh::lean_ctor_set(v___x_4595_, 2, v___x_4593_);
                crate::leanh::lean_ctor_set(v___x_4595_, 3, v___x_4594_);
                crate::leanh::lean_inc_ref(v___x_4590_);
                v___x_4596_ = l_Lean_Syntax_node3(
                    v_a_4582_,
                    v___x_4588_,
                    v_snd_4523_,
                    v___x_4590_,
                    v___x_4595_,
                );
                v___x_4597_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6;
                v___x_4598_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__61;
                v___x_4599_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4599_, 0, v_a_4582_);
                crate::leanh::lean_ctor_set(v___x_4599_, 1, v___x_4598_);
                v___x_4600_ = l_Lean_Syntax_node1(v_a_4582_, v___x_4597_, v___x_4599_);
                v___x_4601_ = l_Lean_Syntax_node3(
                    v_a_4582_,
                    v___x_4588_,
                    v___x_4596_,
                    v___x_4590_,
                    v___x_4600_,
                );
                v___x_4602_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4602_, 0, v_ctorArgs_4529_);
                crate::leanh::lean_ctor_set(v___x_4602_, 1, v___x_4601_);
                v___x_4603_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4603_, 0, v___x_4602_);
                if v_isShared_4585_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4584_, 0, v___x_4603_);
                    v___x_4605_ = v___x_4584_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4606_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___x_4603_);
                    v___x_4605_ = v_reuseFailAlloc_4606_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4605_;
            }
            8 => {
                if v_isShared_4611_ == 0 {
                    v___x_4613_ = v___x_4610_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4614_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_a_4608_);
                    v___x_4613_ = v_reuseFailAlloc_4614_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4613_;
            }
            10 => {
                if v_isShared_4619_ == 0 {
                    v___x_4621_ = v___x_4618_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4622_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4622_, 0, v_a_4616_);
                    v___x_4621_ = v_reuseFailAlloc_4622_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4621_;
            }
            12 => {
                v___x_4630_ = (crate::leanh::lean_unbox(v_a_4626_) as u8);
                crate::leanh::lean_dec(v_a_4626_);
                v___x_4631_ = l_Lean_BinderInfo_isExplicit(v___x_4630_);
                if v___x_4631_ == 0 {
                    crate::leanh::lean_dec(v_auxFunName_4527_);
                    crate::leanh::lean_dec(v___x_4526_);
                    crate::leanh::lean_dec_ref(v___f_4525_);
                    crate::leanh::lean_dec_ref(v___x_4522_);
                    v___x_4632_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4632_, 0, v_ctorArgs_4529_);
                    crate::leanh::lean_ctor_set(v___x_4632_, 1, v_snd_4523_);
                    v___x_4633_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4633_, 0, v___x_4632_);
                    if v_isShared_4629_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4628_, 0, v___x_4633_);
                        v___x_4635_ = v___x_4628_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_4636_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4633_);
                        v___x_4635_ = v_reuseFailAlloc_4636_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4628_);
                    crate::leanh::lean_inc(v___y_4535_);
                    crate::leanh::lean_inc_ref(v___y_4534_);
                    crate::leanh::lean_inc(v___y_4533_);
                    crate::leanh::lean_inc_ref(v___y_4532_);
                    crate::leanh::lean_inc_ref(v___x_4522_);
                    v___x_4637_ = lean_infer_type(
                        v___x_4522_,
                        v___y_4532_,
                        v___y_4533_,
                        v___y_4534_,
                        v___y_4535_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4637_) == 0 {
                        v_a_4638_ = crate::leanh::lean_ctor_get(v___x_4637_, 0);
                        crate::leanh::lean_inc(v_a_4638_);
                        crate::leanh::lean_dec_ref_known(v___x_4637_, 1);
                        v_name_4639_ = crate::leanh::lean_ctor_get(v_toConstantVal_4524_, 0);
                        v___x_4640_ = l_Lean_Expr_isAppOf(v_a_4638_, v_name_4639_);
                        crate::leanh::lean_dec(v_a_4638_);
                        if v___x_4640_ == 0 {
                            crate::leanh::lean_dec(v_auxFunName_4527_);
                            crate::leanh::lean_inc_ref(v___x_4522_);
                            v___x_4641_ = l_Lean_Meta_isType(
                                v___x_4522_,
                                v___y_4532_,
                                v___y_4533_,
                                v___y_4534_,
                                v___y_4535_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4641_) == 0 {
                                v_a_4642_ = crate::leanh::lean_ctor_get(v___x_4641_, 0);
                                crate::leanh::lean_inc(v_a_4642_);
                                v___x_4643_ = (crate::leanh::lean_unbox(v_a_4642_) as u8);
                                crate::leanh::lean_dec(v_a_4642_);
                                if v___x_4643_ == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4641_, 1);
                                    v___x_4644_ = l_Lean_Meta_isProof(
                                        v___x_4522_,
                                        v___y_4532_,
                                        v___y_4533_,
                                        v___y_4534_,
                                        v___y_4535_,
                                    );
                                    v___y_4538_ = v___x_4644_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_4522_);
                                    v___y_4538_ = v___x_4641_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_4522_);
                                v___y_4538_ = v___x_4641_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4522_);
                            crate::leanh::lean_inc(v___y_4535_);
                            crate::leanh::lean_inc_ref(v___y_4534_);
                            crate::leanh::lean_inc(v___y_4533_);
                            crate::leanh::lean_inc_ref(v___y_4532_);
                            crate::leanh::lean_inc(v___y_4531_);
                            crate::leanh::lean_inc_ref(v___y_4530_);
                            v___x_4645_ = crate::leanh::lean_apply_7(
                                v___f_4525_,
                                v___y_4530_,
                                v___y_4531_,
                                v___y_4532_,
                                v___y_4533_,
                                v___y_4534_,
                                v___y_4535_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_4645_) == 0 {
                                v_a_4646_ = crate::leanh::lean_ctor_get(v___x_4645_, 0);
                                v_isSharedCheck_4676_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4645_)) as u8;
                                if v_isSharedCheck_4676_ == 0 {
                                    v___x_4648_ = v___x_4645_;
                                    v_isShared_4649_ = v_isSharedCheck_4676_;
                                    state = 14;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4646_);
                                    crate::leanh::lean_dec(v___x_4645_);
                                    v___x_4648_ = crate::leanh::lean_box(0);
                                    v_isShared_4649_ = v_isSharedCheck_4676_;
                                    state = 14;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_ctorArgs_4529_);
                                crate::leanh::lean_dec(v_auxFunName_4527_);
                                crate::leanh::lean_dec(v___x_4526_);
                                crate::leanh::lean_dec(v_snd_4523_);
                                v_a_4677_ = crate::leanh::lean_ctor_get(v___x_4645_, 0);
                                v_isSharedCheck_4684_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4645_)) as u8;
                                if v_isSharedCheck_4684_ == 0 {
                                    v___x_4679_ = v___x_4645_;
                                    v_isShared_4680_ = v_isSharedCheck_4684_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4677_);
                                    crate::leanh::lean_dec(v___x_4645_);
                                    v___x_4679_ = crate::leanh::lean_box(0);
                                    v_isShared_4680_ = v_isSharedCheck_4684_;
                                    state = 16;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_ctorArgs_4529_);
                        crate::leanh::lean_dec(v_auxFunName_4527_);
                        crate::leanh::lean_dec(v___x_4526_);
                        crate::leanh::lean_dec_ref(v___f_4525_);
                        crate::leanh::lean_dec(v_snd_4523_);
                        crate::leanh::lean_dec_ref(v___x_4522_);
                        v_a_4685_ = crate::leanh::lean_ctor_get(v___x_4637_, 0);
                        v_isSharedCheck_4692_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4637_)) as u8;
                        if v_isSharedCheck_4692_ == 0 {
                            v___x_4687_ = v___x_4637_;
                            v_isShared_4688_ = v_isSharedCheck_4692_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4685_);
                            crate::leanh::lean_dec(v___x_4637_);
                            v___x_4687_ = crate::leanh::lean_box(0);
                            v_isShared_4688_ = v_isSharedCheck_4692_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            13 => {
                return v___x_4635_;
            }
            14 => {
                v_quotContext_4650_ = crate::leanh::lean_ctor_get(v___y_4534_, 10);
                v_currMacroScope_4651_ = crate::leanh::lean_ctor_get(v___y_4534_, 11);
                v___x_4652_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3;
                v___x_4653_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4;
                crate::leanh::lean_inc_n(v_a_4646_, 7);
                v___x_4654_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4654_, 0, v_a_4646_);
                crate::leanh::lean_ctor_set(v___x_4654_, 1, v___x_4653_);
                v___x_4655_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3);
                v___x_4656_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5;
                crate::leanh::lean_inc(v_currMacroScope_4651_);
                crate::leanh::lean_inc(v_quotContext_4650_);
                v___x_4657_ =
                    l_Lean_addMacroScope(v_quotContext_4650_, v___x_4656_, v_currMacroScope_4651_);
                v___x_4658_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10;
                v___x_4659_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4659_, 0, v_a_4646_);
                crate::leanh::lean_ctor_set(v___x_4659_, 1, v___x_4655_);
                crate::leanh::lean_ctor_set(v___x_4659_, 2, v___x_4657_);
                crate::leanh::lean_ctor_set(v___x_4659_, 3, v___x_4658_);
                crate::leanh::lean_inc_ref(v___x_4654_);
                v___x_4660_ = l_Lean_Syntax_node3(
                    v_a_4646_,
                    v___x_4652_,
                    v_snd_4523_,
                    v___x_4654_,
                    v___x_4659_,
                );
                v___x_4661_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33;
                v___x_4662_ = lean_mk_syntax_ident(v_auxFunName_4527_);
                v___x_4663_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9;
                v___x_4664_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6;
                v___x_4665_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7;
                v___x_4666_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4666_, 0, v_a_4646_);
                crate::leanh::lean_ctor_set(v___x_4666_, 1, v___x_4665_);
                v___x_4667_ = l_Lean_Syntax_node1(v_a_4646_, v___x_4664_, v___x_4666_);
                v___x_4668_ = l_Lean_Syntax_node2(v_a_4646_, v___x_4663_, v___x_4526_, v___x_4667_);
                v___x_4669_ = l_Lean_Syntax_node2(v_a_4646_, v___x_4661_, v___x_4662_, v___x_4668_);
                v___x_4670_ = l_Lean_Syntax_node3(
                    v_a_4646_,
                    v___x_4652_,
                    v___x_4660_,
                    v___x_4654_,
                    v___x_4669_,
                );
                v___x_4671_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4671_, 0, v_ctorArgs_4529_);
                crate::leanh::lean_ctor_set(v___x_4671_, 1, v___x_4670_);
                v___x_4672_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4672_, 0, v___x_4671_);
                if v_isShared_4649_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4648_, 0, v___x_4672_);
                    v___x_4674_ = v___x_4648_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4675_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4675_, 0, v___x_4672_);
                    v___x_4674_ = v_reuseFailAlloc_4675_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4674_;
            }
            16 => {
                if v_isShared_4680_ == 0 {
                    v___x_4682_ = v___x_4679_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4683_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_a_4677_);
                    v___x_4682_ = v_reuseFailAlloc_4683_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4682_;
            }
            18 => {
                if v_isShared_4688_ == 0 {
                    v___x_4690_ = v___x_4687_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4691_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4691_, 0, v_a_4685_);
                    v___x_4690_ = v_reuseFailAlloc_4691_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4690_;
            }
            20 => {
                if v_isShared_4697_ == 0 {
                    v___x_4699_ = v___x_4696_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4700_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
                    v___x_4699_ = v_reuseFailAlloc_4700_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4699_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___boxed(
    mut v___x_4702_: *mut crate::leanh::LeanObject,
    mut v_snd_4703_: *mut crate::leanh::LeanObject,
    mut v_toConstantVal_4704_: *mut crate::leanh::LeanObject,
    mut v___f_4705_: *mut crate::leanh::LeanObject,
    mut v___x_4706_: *mut crate::leanh::LeanObject,
    mut v_auxFunName_4707_: *mut crate::leanh::LeanObject,
    mut v_____r_4708_: *mut crate::leanh::LeanObject,
    mut v_ctorArgs_4709_: *mut crate::leanh::LeanObject,
    mut v___y_4710_: *mut crate::leanh::LeanObject,
    mut v___y_4711_: *mut crate::leanh::LeanObject,
    mut v___y_4712_: *mut crate::leanh::LeanObject,
    mut v___y_4713_: *mut crate::leanh::LeanObject,
    mut v___y_4714_: *mut crate::leanh::LeanObject,
    mut v___y_4715_: *mut crate::leanh::LeanObject,
    mut v___y_4716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4717_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(v___x_4702_, v_snd_4703_, v_toConstantVal_4704_, v___f_4705_, v___x_4706_, v_auxFunName_4707_, v_____r_4708_, v_ctorArgs_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
    crate::leanh::lean_dec(v___y_4715_);
    crate::leanh::lean_dec_ref(v___y_4714_);
    crate::leanh::lean_dec(v___y_4713_);
    crate::leanh::lean_dec_ref(v___y_4712_);
    crate::leanh::lean_dec(v___y_4711_);
    crate::leanh::lean_dec_ref(v___y_4710_);
    crate::leanh::lean_dec_ref(v_toConstantVal_4704_);
    return v_res_4717_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(
    mut v_upperBound_4721_: *mut crate::leanh::LeanObject,
    mut v_xs_4722_: *mut crate::leanh::LeanObject,
    mut v_indVal_4723_: *mut crate::leanh::LeanObject,
    mut v_auxFunName_4724_: *mut crate::leanh::LeanObject,
    mut v_header_4725_: *mut crate::leanh::LeanObject,
    mut v_a_4726_: *mut crate::leanh::LeanObject,
    mut v_b_4727_: *mut crate::leanh::LeanObject,
    mut v___y_4728_: *mut crate::leanh::LeanObject,
    mut v___y_4729_: *mut crate::leanh::LeanObject,
    mut v___y_4730_: *mut crate::leanh::LeanObject,
    mut v___y_4731_: *mut crate::leanh::LeanObject,
    mut v___y_4732_: *mut crate::leanh::LeanObject,
    mut v___y_4733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4740_: u8 = 0;
    let mut v_a_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4749_: u8 = 0;
    let mut v_a_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4753_: u8 = 0;
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4757_: u8 = 0;
    let mut v___x_4758_: u8 = 0;
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4764_: u8 = 0;
    let mut v_toConstantVal_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: u8 = 0;
    let mut v_a_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4790_: u8 = 0;
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4794_: u8 = 0;
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4801_: u8 = 0;
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4805_: u8 = 0;
    let mut v_argNames_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4809_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4758_ = lean_nat_dec_lt(v_a_4726_, v_upperBound_4721_);
                if v___x_4758_ == 0 {
                    crate::leanh::lean_dec(v_a_4726_);
                    crate::leanh::lean_dec(v_auxFunName_4724_);
                    v___x_4759_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4759_, 0, v_b_4727_);
                    return v___x_4759_;
                } else {
                    v_fst_4760_ = crate::leanh::lean_ctor_get(v_b_4727_, 0);
                    v_snd_4761_ = crate::leanh::lean_ctor_get(v_b_4727_, 1);
                    v_isSharedCheck_4809_ = (!crate::leanh::lean_is_exclusive(v_b_4727_)) as u8;
                    if v_isSharedCheck_4809_ == 0 {
                        v___x_4763_ = v_b_4727_;
                        v_isShared_4764_ = v_isSharedCheck_4809_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4761_);
                        crate::leanh::lean_inc(v_fst_4760_);
                        crate::leanh::lean_dec(v_b_4727_);
                        v___x_4763_ = crate::leanh::lean_box(0);
                        v_isShared_4764_ = v_isSharedCheck_4809_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_4736_) == 0 {
                    v_a_4737_ = crate::leanh::lean_ctor_get(v___y_4736_, 0);
                    v_isSharedCheck_4749_ = (!crate::leanh::lean_is_exclusive(v___y_4736_)) as u8;
                    if v_isSharedCheck_4749_ == 0 {
                        v___x_4739_ = v___y_4736_;
                        v_isShared_4740_ = v_isSharedCheck_4749_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4737_);
                        crate::leanh::lean_dec(v___y_4736_);
                        v___x_4739_ = crate::leanh::lean_box(0);
                        v_isShared_4740_ = v_isSharedCheck_4749_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4726_);
                    crate::leanh::lean_dec(v_auxFunName_4724_);
                    v_a_4750_ = crate::leanh::lean_ctor_get(v___y_4736_, 0);
                    v_isSharedCheck_4757_ = (!crate::leanh::lean_is_exclusive(v___y_4736_)) as u8;
                    if v_isSharedCheck_4757_ == 0 {
                        v___x_4752_ = v___y_4736_;
                        v_isShared_4753_ = v_isSharedCheck_4757_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4750_);
                        crate::leanh::lean_dec(v___y_4736_);
                        v___x_4752_ = crate::leanh::lean_box(0);
                        v_isShared_4753_ = v_isSharedCheck_4757_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4737_) == 0 {
                    crate::leanh::lean_dec(v_a_4726_);
                    crate::leanh::lean_dec(v_auxFunName_4724_);
                    v_a_4741_ = crate::leanh::lean_ctor_get(v_a_4737_, 0);
                    crate::leanh::lean_inc(v_a_4741_);
                    crate::leanh::lean_dec_ref_known(v_a_4737_, 1);
                    if v_isShared_4740_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4739_, 0, v_a_4741_);
                        v___x_4743_ = v___x_4739_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4744_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_a_4741_);
                        v___x_4743_ = v_reuseFailAlloc_4744_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4739_);
                    v_a_4745_ = crate::leanh::lean_ctor_get(v_a_4737_, 0);
                    crate::leanh::lean_inc(v_a_4745_);
                    crate::leanh::lean_dec_ref_known(v_a_4737_, 1);
                    v___x_4746_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4747_ = lean_nat_add(v_a_4726_, v___x_4746_);
                    crate::leanh::lean_dec(v_a_4726_);
                    v_a_4726_ = v___x_4747_;
                    v_b_4727_ = v_a_4745_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_4743_;
            }
            4 => {
                if v_isShared_4753_ == 0 {
                    v___x_4755_ = v___x_4752_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4756_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_a_4750_);
                    v___x_4755_ = v_reuseFailAlloc_4756_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4755_;
            }
            6 => {
                v_toConstantVal_4765_ = crate::leanh::lean_ctor_get(v_indVal_4723_, 0);
                v_numParams_4766_ = crate::leanh::lean_ctor_get(v_indVal_4723_, 1);
                v___f_4767_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__0;
                v___x_4768_ = lean_array_fget_borrowed(v_xs_4722_, v_a_4726_);
                v___x_4769_ = lean_nat_dec_lt(v_a_4726_, v_numParams_4766_);
                if v___x_4769_ == 0 {
                    v___x_4795_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__1;
                    v___x_4796_ =
                        l_Lean_Core_mkFreshUserName(v___x_4795_, v___y_4732_, v___y_4733_);
                    if crate::leanh::lean_obj_tag(v___x_4796_) == 0 {
                        v_a_4797_ = crate::leanh::lean_ctor_get(v___x_4796_, 0);
                        crate::leanh::lean_inc(v_a_4797_);
                        crate::leanh::lean_dec_ref_known(v___x_4796_, 1);
                        v_a_4771_ = v_a_4797_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_4763_);
                        crate::leanh::lean_dec(v_snd_4761_);
                        crate::leanh::lean_dec(v_fst_4760_);
                        crate::leanh::lean_dec(v_a_4726_);
                        crate::leanh::lean_dec(v_auxFunName_4724_);
                        v_a_4798_ = crate::leanh::lean_ctor_get(v___x_4796_, 0);
                        v_isSharedCheck_4805_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4796_)) as u8;
                        if v_isSharedCheck_4805_ == 0 {
                            v___x_4800_ = v___x_4796_;
                            v_isShared_4801_ = v_isSharedCheck_4805_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4798_);
                            crate::leanh::lean_dec(v___x_4796_);
                            v___x_4800_ = crate::leanh::lean_box(0);
                            v_isShared_4801_ = v_isSharedCheck_4805_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    v_argNames_4806_ = crate::leanh::lean_ctor_get(v_header_4725_, 1);
                    v___x_4807_ = crate::leanh::lean_box(0);
                    v___x_4808_ = lean_array_get_borrowed(v___x_4807_, v_argNames_4806_, v_a_4726_);
                    crate::leanh::lean_inc(v___x_4808_);
                    v_a_4771_ = v___x_4808_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4772_ = lean_mk_syntax_ident(v_a_4771_);
                if v___x_4769_ == 0 {
                    crate::leanh::lean_del_object(v___x_4763_);
                    crate::leanh::lean_inc(v___x_4772_);
                    v___x_4773_ = lean_array_push(v_fst_4760_, v___x_4772_);
                    v___x_4774_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_auxFunName_4724_);
                    crate::leanh::lean_inc(v___x_4768_);
                    v___x_4775_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(v___x_4768_, v_snd_4761_, v_toConstantVal_4765_, v___f_4767_, v___x_4772_, v_auxFunName_4724_, v___x_4774_, v___x_4773_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_);
                    v___y_4736_ = v___x_4775_;
                    state = 1;
                    continue;
                } else {
                    v___x_4776_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0(v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_);
                    if crate::leanh::lean_obj_tag(v___x_4776_) == 0 {
                        v_a_4777_ = crate::leanh::lean_ctor_get(v___x_4776_, 0);
                        crate::leanh::lean_inc_n(v_a_4777_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_4776_, 1);
                        v___x_4778_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1;
                        v___x_4779_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2;
                        if v_isShared_4764_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_4763_, 2);
                            crate::leanh::lean_ctor_set(v___x_4763_, 1, v___x_4779_);
                            crate::leanh::lean_ctor_set(v___x_4763_, 0, v_a_4777_);
                            v___x_4781_ = v___x_4763_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_4786_ =
                                crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_a_4777_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4786_, 1, v___x_4779_);
                            v___x_4781_ = v_reuseFailAlloc_4786_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4772_);
                        crate::leanh::lean_del_object(v___x_4763_);
                        crate::leanh::lean_dec(v_snd_4761_);
                        crate::leanh::lean_dec(v_fst_4760_);
                        crate::leanh::lean_dec(v_a_4726_);
                        crate::leanh::lean_dec(v_auxFunName_4724_);
                        v_a_4787_ = crate::leanh::lean_ctor_get(v___x_4776_, 0);
                        v_isSharedCheck_4794_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4776_)) as u8;
                        if v_isSharedCheck_4794_ == 0 {
                            v___x_4789_ = v___x_4776_;
                            v_isShared_4790_ = v_isSharedCheck_4794_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4787_);
                            crate::leanh::lean_dec(v___x_4776_);
                            v___x_4789_ = crate::leanh::lean_box(0);
                            v_isShared_4790_ = v_isSharedCheck_4794_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            8 => {
                v___x_4782_ = l_Lean_Syntax_node1(v_a_4777_, v___x_4778_, v___x_4781_);
                v___x_4783_ = lean_array_push(v_fst_4760_, v___x_4782_);
                v___x_4784_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_auxFunName_4724_);
                crate::leanh::lean_inc(v___x_4768_);
                v___x_4785_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(v___x_4768_, v_snd_4761_, v_toConstantVal_4765_, v___f_4767_, v___x_4772_, v_auxFunName_4724_, v___x_4784_, v___x_4783_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_);
                v___y_4736_ = v___x_4785_;
                state = 1;
                continue;
            }
            9 => {
                if v_isShared_4790_ == 0 {
                    v___x_4792_ = v___x_4789_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4793_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_a_4787_);
                    v___x_4792_ = v_reuseFailAlloc_4793_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4792_;
            }
            11 => {
                if v_isShared_4801_ == 0 {
                    v___x_4803_ = v___x_4800_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4804_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4798_);
                    v___x_4803_ = v_reuseFailAlloc_4804_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___boxed(
    mut v_upperBound_4810_: *mut crate::leanh::LeanObject,
    mut v_xs_4811_: *mut crate::leanh::LeanObject,
    mut v_indVal_4812_: *mut crate::leanh::LeanObject,
    mut v_auxFunName_4813_: *mut crate::leanh::LeanObject,
    mut v_header_4814_: *mut crate::leanh::LeanObject,
    mut v_a_4815_: *mut crate::leanh::LeanObject,
    mut v_b_4816_: *mut crate::leanh::LeanObject,
    mut v___y_4817_: *mut crate::leanh::LeanObject,
    mut v___y_4818_: *mut crate::leanh::LeanObject,
    mut v___y_4819_: *mut crate::leanh::LeanObject,
    mut v___y_4820_: *mut crate::leanh::LeanObject,
    mut v___y_4821_: *mut crate::leanh::LeanObject,
    mut v___y_4822_: *mut crate::leanh::LeanObject,
    mut v___y_4823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4824_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(v_upperBound_4810_, v_xs_4811_, v_indVal_4812_, v_auxFunName_4813_, v_header_4814_, v_a_4815_, v_b_4816_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_);
    crate::leanh::lean_dec(v___y_4822_);
    crate::leanh::lean_dec_ref(v___y_4821_);
    crate::leanh::lean_dec(v___y_4820_);
    crate::leanh::lean_dec_ref(v___y_4819_);
    crate::leanh::lean_dec(v___y_4818_);
    crate::leanh::lean_dec_ref(v___y_4817_);
    crate::leanh::lean_dec_ref(v_header_4814_);
    crate::leanh::lean_dec_ref(v_indVal_4812_);
    crate::leanh::lean_dec_ref(v_xs_4811_);
    crate::leanh::lean_dec(v_upperBound_4810_);
    return v_res_4824_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4837_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__4;
    v___x_4838_ = l_String_toRawSubstring_x27(v___x_4837_);
    return v___x_4838_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4862_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__15;
    v___x_4863_ = l_Lean_mkAtom(v___x_4862_);
    return v___x_4863_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4866_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__18;
    v___x_4867_ = l_String_toRawSubstring_x27(v___x_4866_);
    return v___x_4867_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1(
    mut v_indVal_4923_: *mut crate::leanh::LeanObject,
    mut v___x_4924_: *mut crate::leanh::LeanObject,
    mut v_alts_4925_: *mut crate::leanh::LeanObject,
    mut v_name_4926_: *mut crate::leanh::LeanObject,
    mut v_auxFunName_4927_: *mut crate::leanh::LeanObject,
    mut v_header_4928_: *mut crate::leanh::LeanObject,
    mut v___f_4929_: *mut crate::leanh::LeanObject,
    mut v_head_4930_: *mut crate::leanh::LeanObject,
    mut v_xs_4931_: *mut crate::leanh::LeanObject,
    mut v_x_4932_: *mut crate::leanh::LeanObject,
    mut v___y_4933_: *mut crate::leanh::LeanObject,
    mut v___y_4934_: *mut crate::leanh::LeanObject,
    mut v___y_4935_: *mut crate::leanh::LeanObject,
    mut v___y_4936_: *mut crate::leanh::LeanObject,
    mut v___y_4937_: *mut crate::leanh::LeanObject,
    mut v___y_4938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numIndices_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: u8 = 0;
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: u8 = 0;
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4972_: u8 = 0;
    let mut v_fst_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4977_: u8 = 0;
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4992_: usize = 0;
    let mut v___x_4993_: usize = 0;
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5073_: u8 = 0;
    let mut v_isSharedCheck_5074_: u8 = 0;
    let mut v_a_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5078_: u8 = 0;
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5082_: u8 = 0;
    let mut v_a_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5086_: u8 = 0;
    let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5090_: u8 = 0;
    let mut v_a_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5094_: u8 = 0;
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5098_: u8 = 0;
    let mut v_a_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5102_: u8 = 0;
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_numIndices_4940_ = crate::leanh::lean_ctor_get(v_indVal_4923_, 2);
                crate::leanh::lean_inc_ref(v_alts_4925_);
                crate::leanh::lean_inc(v___x_4924_);
                v___x_4941_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(v_numIndices_4940_, v___x_4924_, v_alts_4925_, v___y_4937_);
                if crate::leanh::lean_obj_tag(v___x_4941_) == 0 {
                    v_a_4942_ = crate::leanh::lean_ctor_get(v___x_4941_, 0);
                    crate::leanh::lean_inc(v_a_4942_);
                    crate::leanh::lean_dec_ref_known(v___x_4941_, 1);
                    v_ref_4943_ = crate::leanh::lean_ctor_get(v___y_4937_, 5);
                    v_quotContext_4944_ = crate::leanh::lean_ctor_get(v___y_4937_, 10);
                    v_currMacroScope_4945_ = crate::leanh::lean_ctor_get(v___y_4937_, 11);
                    v___x_4946_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1;
                    v___x_4947_ = crate::leanh::lean_box(0);
                    v___x_4948_ = lean_array_get_size(v_xs_4931_);
                    v___x_4949_ = 0;
                    v___x_4950_ = l_Lean_SourceInfo_fromRef(v_ref_4943_, v___x_4949_);
                    v___x_4951_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5);
                    crate::leanh::lean_inc(v_currMacroScope_4945_);
                    crate::leanh::lean_inc(v_quotContext_4944_);
                    v___x_4952_ = l_Lean_addMacroScope(
                        v_quotContext_4944_,
                        v___x_4946_,
                        v_currMacroScope_4945_,
                    );
                    v___x_4953_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__8;
                    crate::leanh::lean_inc_n(v___x_4950_, 2);
                    v___x_4954_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4954_, 0, v___x_4950_);
                    crate::leanh::lean_ctor_set(v___x_4954_, 1, v___x_4951_);
                    crate::leanh::lean_ctor_set(v___x_4954_, 2, v___x_4952_);
                    crate::leanh::lean_ctor_set(v___x_4954_, 3, v___x_4953_);
                    v___x_4955_ = 1;
                    v___x_4956_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_4926_,
                        v___x_4955_,
                    );
                    v___x_4957_ = crate::leanh::lean_box(2);
                    v___x_4958_ = l_Lean_Syntax_mkStrLit(v___x_4956_, v___x_4957_);
                    v___x_4959_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9;
                    v___x_4960_ = l_Lean_Syntax_node1(v___x_4950_, v___x_4959_, v___x_4958_);
                    v___x_4961_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33;
                    v___x_4962_ =
                        l_Lean_Syntax_node2(v___x_4950_, v___x_4961_, v___x_4954_, v___x_4960_);
                    v___x_4963_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4963_, 0, v_alts_4925_);
                    crate::leanh::lean_ctor_set(v___x_4963_, 1, v___x_4962_);
                    v___x_4964_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(v___x_4948_, v_xs_4931_, v_indVal_4923_, v_auxFunName_4927_, v_header_4928_, v___x_4924_, v___x_4963_, v___y_4933_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_);
                    if crate::leanh::lean_obj_tag(v___x_4964_) == 0 {
                        v_a_4965_ = crate::leanh::lean_ctor_get(v___x_4964_, 0);
                        crate::leanh::lean_inc(v_a_4965_);
                        crate::leanh::lean_dec_ref_known(v___x_4964_, 1);
                        crate::leanh::lean_inc_ref(v___f_4929_);
                        crate::leanh::lean_inc(v___y_4938_);
                        crate::leanh::lean_inc_ref(v___y_4937_);
                        crate::leanh::lean_inc(v___y_4936_);
                        crate::leanh::lean_inc_ref(v___y_4935_);
                        crate::leanh::lean_inc(v___y_4934_);
                        crate::leanh::lean_inc_ref(v___y_4933_);
                        v___x_4966_ = crate::leanh::lean_apply_7(
                            v___f_4929_,
                            v___y_4933_,
                            v___y_4934_,
                            v___y_4935_,
                            v___y_4936_,
                            v___y_4937_,
                            v___y_4938_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_4966_) == 0 {
                            v_a_4967_ = crate::leanh::lean_ctor_get(v___x_4966_, 0);
                            crate::leanh::lean_inc(v_a_4967_);
                            crate::leanh::lean_dec_ref_known(v___x_4966_, 1);
                            crate::leanh::lean_inc(v___y_4938_);
                            crate::leanh::lean_inc_ref(v___y_4937_);
                            crate::leanh::lean_inc(v___y_4936_);
                            crate::leanh::lean_inc_ref(v___y_4935_);
                            crate::leanh::lean_inc(v___y_4934_);
                            crate::leanh::lean_inc_ref(v___y_4933_);
                            v___x_4968_ = crate::leanh::lean_apply_7(
                                v___f_4929_,
                                v___y_4933_,
                                v___y_4934_,
                                v___y_4935_,
                                v___y_4936_,
                                v___y_4937_,
                                v___y_4938_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_4968_) == 0 {
                                v_a_4969_ = crate::leanh::lean_ctor_get(v___x_4968_, 0);
                                v_isSharedCheck_5074_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4968_)) as u8;
                                if v_isSharedCheck_5074_ == 0 {
                                    v___x_4971_ = v___x_4968_;
                                    v_isShared_4972_ = v_isSharedCheck_5074_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4969_);
                                    crate::leanh::lean_dec(v___x_4968_);
                                    v___x_4971_ = crate::leanh::lean_box(0);
                                    v_isShared_4972_ = v_isSharedCheck_5074_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_4967_);
                                crate::leanh::lean_dec(v_a_4965_);
                                crate::leanh::lean_dec(v_a_4942_);
                                crate::leanh::lean_dec(v_head_4930_);
                                v_a_5075_ = crate::leanh::lean_ctor_get(v___x_4968_, 0);
                                v_isSharedCheck_5082_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4968_)) as u8;
                                if v_isSharedCheck_5082_ == 0 {
                                    v___x_5077_ = v___x_4968_;
                                    v_isShared_5078_ = v_isSharedCheck_5082_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5075_);
                                    crate::leanh::lean_dec(v___x_4968_);
                                    v___x_5077_ = crate::leanh::lean_box(0);
                                    v_isShared_5078_ = v_isSharedCheck_5082_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4965_);
                            crate::leanh::lean_dec(v_a_4942_);
                            crate::leanh::lean_dec(v_head_4930_);
                            crate::leanh::lean_dec_ref(v___f_4929_);
                            v_a_5083_ = crate::leanh::lean_ctor_get(v___x_4966_, 0);
                            v_isSharedCheck_5090_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4966_)) as u8;
                            if v_isSharedCheck_5090_ == 0 {
                                v___x_5085_ = v___x_4966_;
                                v_isShared_5086_ = v_isSharedCheck_5090_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5083_);
                                crate::leanh::lean_dec(v___x_4966_);
                                v___x_5085_ = crate::leanh::lean_box(0);
                                v_isShared_5086_ = v_isSharedCheck_5090_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4942_);
                        crate::leanh::lean_dec(v_head_4930_);
                        crate::leanh::lean_dec_ref(v___f_4929_);
                        v_a_5091_ = crate::leanh::lean_ctor_get(v___x_4964_, 0);
                        v_isSharedCheck_5098_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4964_)) as u8;
                        if v_isSharedCheck_5098_ == 0 {
                            v___x_5093_ = v___x_4964_;
                            v_isShared_5094_ = v_isSharedCheck_5098_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5091_);
                            crate::leanh::lean_dec(v___x_4964_);
                            v___x_5093_ = crate::leanh::lean_box(0);
                            v_isShared_5094_ = v_isSharedCheck_5098_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_head_4930_);
                    crate::leanh::lean_dec_ref(v___f_4929_);
                    crate::leanh::lean_dec(v_auxFunName_4927_);
                    crate::leanh::lean_dec(v_name_4926_);
                    crate::leanh::lean_dec_ref(v_alts_4925_);
                    crate::leanh::lean_dec(v___x_4924_);
                    v_a_5099_ = crate::leanh::lean_ctor_get(v___x_4941_, 0);
                    v_isSharedCheck_5106_ = (!crate::leanh::lean_is_exclusive(v___x_4941_)) as u8;
                    if v_isSharedCheck_5106_ == 0 {
                        v___x_5101_ = v___x_4941_;
                        v_isShared_5102_ = v_isSharedCheck_5106_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5099_);
                        crate::leanh::lean_dec(v___x_4941_);
                        v___x_5101_ = crate::leanh::lean_box(0);
                        v_isShared_5102_ = v_isSharedCheck_5106_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4973_ = crate::leanh::lean_ctor_get(v_a_4965_, 0);
                v_snd_4974_ = crate::leanh::lean_ctor_get(v_a_4965_, 1);
                v_isSharedCheck_5073_ = (!crate::leanh::lean_is_exclusive(v_a_4965_)) as u8;
                if v_isSharedCheck_5073_ == 0 {
                    v___x_4976_ = v_a_4965_;
                    v_isShared_4977_ = v_isSharedCheck_5073_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4974_);
                    crate::leanh::lean_inc(v_fst_4973_);
                    crate::leanh::lean_dec(v_a_4965_);
                    v___x_4976_ = crate::leanh::lean_box(0);
                    v_isShared_4977_ = v_isSharedCheck_5073_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4978_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__9;
                crate::leanh::lean_inc(v_a_4967_);
                if v_isShared_4977_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4976_, 2);
                    crate::leanh::lean_ctor_set(v___x_4976_, 1, v___x_4978_);
                    crate::leanh::lean_ctor_set(v___x_4976_, 0, v_a_4967_);
                    v___x_4980_ = v___x_4976_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5072_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5072_, 0, v_a_4967_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5072_, 1, v___x_4978_);
                    v___x_4980_ = v_reuseFailAlloc_5072_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4981_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11;
                v___x_4982_ = lean_mk_syntax_ident(v_head_4930_);
                crate::leanh::lean_inc_n(v_a_4967_, 2);
                v___x_4983_ = l_Lean_Syntax_node2(v_a_4967_, v___x_4981_, v___x_4980_, v___x_4982_);
                v___x_4984_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once
                    ),
                    _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22,
                );
                v___x_4985_ = l_Array_append___redArg(v___x_4984_, v_fst_4973_);
                crate::leanh::lean_dec(v_fst_4973_);
                v___x_4986_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4986_, 0, v_a_4967_);
                crate::leanh::lean_ctor_set(v___x_4986_, 1, v___x_4959_);
                crate::leanh::lean_ctor_set(v___x_4986_, 2, v___x_4985_);
                v___x_4987_ = l_Lean_Syntax_node2(v_a_4967_, v___x_4961_, v___x_4983_, v___x_4986_);
                v___x_4988_ = lean_array_push(v_a_4942_, v___x_4987_);
                v___x_4989_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13;
                v___x_4990_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__14;
                crate::leanh::lean_inc_n(v_a_4969_, 35);
                v___x_4991_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4991_, 0, v_a_4969_);
                crate::leanh::lean_ctor_set(v___x_4991_, 1, v___x_4990_);
                v_sz_4992_ = lean_array_size(v___x_4988_);
                v___x_4993_ = 0usize;
                v___x_4994_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(v_sz_4992_, v___x_4993_, v___x_4988_);
                v___x_4995_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16);
                v___x_4996_ = l_Lean_mkSepArray(v___x_4994_, v___x_4995_);
                crate::leanh::lean_dec_ref(v___x_4994_);
                v___x_4997_ = l_Array_append___redArg(v___x_4984_, v___x_4996_);
                crate::leanh::lean_dec_ref(v___x_4996_);
                v___x_4998_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4998_, 0, v_a_4969_);
                crate::leanh::lean_ctor_set(v___x_4998_, 1, v___x_4959_);
                crate::leanh::lean_ctor_set(v___x_4998_, 2, v___x_4997_);
                v___x_4999_ = l_Lean_Syntax_node1(v_a_4969_, v___x_4959_, v___x_4998_);
                v___x_5000_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__17;
                v___x_5001_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5001_, 0, v_a_4969_);
                crate::leanh::lean_ctor_set(v___x_5001_, 1, v___x_5000_);
                v___x_5002_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19);
                v___x_5003_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21;
                crate::leanh::lean_inc_n(v_currMacroScope_4945_, 5);
                crate::leanh::lean_inc_n(v_quotContext_4944_, 5);
                v___x_5004_ =
                    l_Lean_addMacroScope(v_quotContext_4944_, v___x_5003_, v_currMacroScope_4945_);
                v___x_5005_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__23;
                v___x_5006_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5006_, 0, v_a_4969_);
                crate::leanh::lean_ctor_set(v___x_5006_, 1, v___x_5002_);
                crate::leanh::lean_ctor_set(v___x_5006_, 2, v___x_5004_);
                crate::leanh::lean_ctor_set(v___x_5006_, 3, v___x_5005_);
                v___x_5007_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9;
                v___x_5008_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11;
                v___x_5009_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7;
                v___x_5010_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5010_, 0, v_a_4969_);
                crate::leanh::lean_ctor_set(v___x_5010_, 1, v___x_5009_);
                v___x_5011_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13;
                v___x_5012_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15);
                v___x_5013_ = crate::leanh::lean_box(0);
                v___x_5014_ =
                    l_Lean_addMacroScope(v_quotContext_4944_, v___x_5013_, v_currMacroScope_4945_);
                v___x_5015_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27;
                v___x_5016_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5016_, 0, v_a_4969_);
                crate::leanh::lean_ctor_set(v___x_5016_, 1, v___x_5012_);
                crate::leanh::lean_ctor_set(v___x_5016_, 2, v___x_5014_);
                crate::leanh::lean_ctor_set(v___x_5016_, 3, v___x_5015_);
                v___x_5017_ = l_Lean_Syntax_node1(v_a_4969_, v___x_5011_, v___x_5016_);
                v___x_5018_ = l_Lean_Syntax_node2(v_a_4969_, v___x_5008_, v___x_5010_, v___x_5017_);
                v___x_5019_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35);
                v___x_5020_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38;
                v___x_5021_ =
                    l_Lean_addMacroScope(v_quotContext_4944_, v___x_5020_, v_currMacroScope_4945_);
                v___x_5022_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30;
                v___x_5023_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5023_, 0, v_a_4969_);
                crate::leanh::lean_ctor_set(v___x_5023_, 1, v___x_5019_);
                crate::leanh::lean_ctor_set(v___x_5023_, 2, v___x_5021_);
                crate::leanh::lean_ctor_set(v___x_5023_, 3, v___x_5022_);
                v___x_5024_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45);
                v___x_5025_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47;
                v___x_5026_ =
                    l_Lean_addMacroScope(v_quotContext_4944_, v___x_5025_, v_currMacroScope_4945_);
                v___x_5027_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__33;
                v___x_5028_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5028_, 0, v_a_4969_);
                crate::leanh::lean_ctor_set(v___x_5028_, 1, v___x_5024_);
                crate::leanh::lean_ctor_set(v___x_5028_, 2, v___x_5026_);
                crate::leanh::lean_ctor_set(v___x_5028_, 3, v___x_5027_);
                v___x_5029_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__35;
                v___x_5030_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__36;
                v___x_5031_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5031_, 0, v_a_4969_);
                crate::leanh::lean_ctor_set(v___x_5031_, 1, v___x_5030_);
                v___x_5032_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__38;
                v___x_5033_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11_once
                    ),
                    _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11,
                );
                v___x_5034_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12;
                v___x_5035_ =
                    l_Lean_addMacroScope(v_quotContext_4944_, v___x_5034_, v_currMacroScope_4945_);
                v___x_5036_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5036_, 0, v_a_4969_);
                crate::leanh::lean_ctor_set(v___x_5036_, 1, v___x_5033_);
                crate::leanh::lean_ctor_set(v___x_5036_, 2, v___x_5035_);
                crate::leanh::lean_ctor_set(v___x_5036_, 3, v___x_4947_);
                v___x_5037_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__39;
                v___x_5038_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5038_, 0, v_a_4969_);
                crate::leanh::lean_ctor_set(v___x_5038_, 1, v___x_5037_);
                v___x_5039_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6;
                v___x_5040_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7;
                v___x_5041_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5041_, 0, v_a_4969_);
                crate::leanh::lean_ctor_set(v___x_5041_, 1, v___x_5040_);
                v___x_5042_ = l_Lean_Syntax_node1(v_a_4969_, v___x_5039_, v___x_5041_);
                crate::leanh::lean_inc_ref(v___x_5036_);
                v___x_5043_ = l_Lean_Syntax_node3(
                    v_a_4969_,
                    v___x_5032_,
                    v___x_5036_,
                    v___x_5038_,
                    v___x_5042_,
                );
                v___x_5044_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__40;
                v___x_5045_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5045_, 0, v_a_4969_);
                crate::leanh::lean_ctor_set(v___x_5045_, 1, v___x_5044_);
                v___x_5046_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__42;
                v___x_5047_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__43;
                v___x_5048_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5048_, 0, v_a_4969_);
                crate::leanh::lean_ctor_set(v___x_5048_, 1, v___x_5047_);
                v___x_5049_ = l_Lean_Syntax_node1(v_a_4969_, v___x_5046_, v___x_5048_);
                v___x_5050_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__44;
                v___x_5051_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5051_, 0, v_a_4969_);
                crate::leanh::lean_ctor_set(v___x_5051_, 1, v___x_5050_);
                v___x_5052_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__45;
                v___x_5053_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5053_, 0, v_a_4969_);
                crate::leanh::lean_ctor_set(v___x_5053_, 1, v___x_5052_);
                v___x_5054_ = l_Lean_Syntax_node1(v_a_4969_, v___x_5046_, v___x_5053_);
                v___x_5055_ = l_Lean_Syntax_node6(
                    v_a_4969_,
                    v___x_5029_,
                    v___x_5031_,
                    v___x_5043_,
                    v___x_5045_,
                    v___x_5049_,
                    v___x_5051_,
                    v___x_5054_,
                );
                v___x_5056_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23;
                v___x_5057_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5057_, 0, v_a_4969_);
                crate::leanh::lean_ctor_set(v___x_5057_, 1, v___x_5056_);
                crate::leanh::lean_inc_ref_n(v___x_5057_, 3);
                crate::leanh::lean_inc_n(v___x_5018_, 3);
                v___x_5058_ = l_Lean_Syntax_node3(
                    v_a_4969_,
                    v___x_5007_,
                    v___x_5018_,
                    v___x_5055_,
                    v___x_5057_,
                );
                v___x_5059_ = l_Lean_Syntax_node3(
                    v_a_4969_,
                    v___x_5007_,
                    v___x_5018_,
                    v_snd_4974_,
                    v___x_5057_,
                );
                v___x_5060_ = l_Lean_Syntax_node2(v_a_4969_, v___x_4959_, v___x_5058_, v___x_5059_);
                v___x_5061_ = l_Lean_Syntax_node2(v_a_4969_, v___x_4961_, v___x_5028_, v___x_5060_);
                v___x_5062_ = l_Lean_Syntax_node3(
                    v_a_4969_,
                    v___x_5007_,
                    v___x_5018_,
                    v___x_5061_,
                    v___x_5057_,
                );
                v___x_5063_ = l_Lean_Syntax_node1(v_a_4969_, v___x_4959_, v___x_5062_);
                v___x_5064_ = l_Lean_Syntax_node2(v_a_4969_, v___x_4961_, v___x_5023_, v___x_5063_);
                v___x_5065_ = l_Lean_Syntax_node3(
                    v_a_4969_,
                    v___x_5007_,
                    v___x_5018_,
                    v___x_5064_,
                    v___x_5057_,
                );
                v___x_5066_ = l_Lean_Syntax_node2(v_a_4969_, v___x_4959_, v___x_5065_, v___x_5036_);
                v___x_5067_ = l_Lean_Syntax_node2(v_a_4969_, v___x_4961_, v___x_5006_, v___x_5066_);
                v___x_5068_ = l_Lean_Syntax_node4(
                    v_a_4969_,
                    v___x_4989_,
                    v___x_4991_,
                    v___x_4999_,
                    v___x_5001_,
                    v___x_5067_,
                );
                if v_isShared_4972_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4971_, 0, v___x_5068_);
                    v___x_5070_ = v___x_4971_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5071_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5071_, 0, v___x_5068_);
                    v___x_5070_ = v_reuseFailAlloc_5071_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5070_;
            }
            5 => {
                if v_isShared_5078_ == 0 {
                    v___x_5080_ = v___x_5077_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5081_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5081_, 0, v_a_5075_);
                    v___x_5080_ = v_reuseFailAlloc_5081_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5080_;
            }
            7 => {
                if v_isShared_5086_ == 0 {
                    v___x_5088_ = v___x_5085_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5089_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5089_, 0, v_a_5083_);
                    v___x_5088_ = v_reuseFailAlloc_5089_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5088_;
            }
            9 => {
                if v_isShared_5094_ == 0 {
                    v___x_5096_ = v___x_5093_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5097_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5097_, 0, v_a_5091_);
                    v___x_5096_ = v_reuseFailAlloc_5097_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5096_;
            }
            11 => {
                if v_isShared_5102_ == 0 {
                    v___x_5104_ = v___x_5101_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5105_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_a_5099_);
                    v___x_5104_ = v_reuseFailAlloc_5105_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_indVal_5107_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_5108_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_alts_5109_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_name_5110_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_auxFunName_5111_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_header_5112_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___f_5113_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_head_5114_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_xs_5115_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_x_5116_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_5117_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_5118_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_5119_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5120_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5121_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5122_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5123_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5124_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1(v_indVal_5107_, v___x_5108_, v_alts_5109_, v_name_5110_, v_auxFunName_5111_, v_header_5112_, v___f_5113_, v_head_5114_, v_xs_5115_, v_x_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_);
    crate::leanh::lean_dec(v___y_5122_);
    crate::leanh::lean_dec_ref(v___y_5121_);
    crate::leanh::lean_dec(v___y_5120_);
    crate::leanh::lean_dec_ref(v___y_5119_);
    crate::leanh::lean_dec(v___y_5118_);
    crate::leanh::lean_dec_ref(v___y_5117_);
    crate::leanh::lean_dec_ref(v_x_5116_);
    crate::leanh::lean_dec_ref(v_xs_5115_);
    crate::leanh::lean_dec_ref(v_header_5112_);
    crate::leanh::lean_dec_ref(v_indVal_5107_);
    return v_res_5124_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0(
    mut v___y_5125_: *mut crate::leanh::LeanObject,
    mut v___y_5126_: *mut crate::leanh::LeanObject,
    mut v___y_5127_: *mut crate::leanh::LeanObject,
    mut v___y_5128_: *mut crate::leanh::LeanObject,
    mut v___y_5129_: *mut crate::leanh::LeanObject,
    mut v___y_5130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: u8 = 0;
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_5132_ = crate::leanh::lean_ctor_get(v___y_5129_, 5);
    v___x_5133_ = 0;
    v___x_5134_ = l_Lean_SourceInfo_fromRef(v_ref_5132_, v___x_5133_);
    v___x_5135_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5135_, 0, v___x_5134_);
    return v___x_5135_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0___boxed(
    mut v___y_5136_: *mut crate::leanh::LeanObject,
    mut v___y_5137_: *mut crate::leanh::LeanObject,
    mut v___y_5138_: *mut crate::leanh::LeanObject,
    mut v___y_5139_: *mut crate::leanh::LeanObject,
    mut v___y_5140_: *mut crate::leanh::LeanObject,
    mut v___y_5141_: *mut crate::leanh::LeanObject,
    mut v___y_5142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5143_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0(v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_);
    crate::leanh::lean_dec(v___y_5141_);
    crate::leanh::lean_dec_ref(v___y_5140_);
    crate::leanh::lean_dec(v___y_5139_);
    crate::leanh::lean_dec_ref(v___y_5138_);
    crate::leanh::lean_dec(v___y_5137_);
    crate::leanh::lean_dec_ref(v___y_5136_);
    return v_res_5143_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(
    mut v_indVal_5147_: *mut crate::leanh::LeanObject,
    mut v_auxFunName_5148_: *mut crate::leanh::LeanObject,
    mut v_header_5149_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5150_: *mut crate::leanh::LeanObject,
    mut v_b_5151_: *mut crate::leanh::LeanObject,
    mut v___y_5152_: *mut crate::leanh::LeanObject,
    mut v___y_5153_: *mut crate::leanh::LeanObject,
    mut v___y_5154_: *mut crate::leanh::LeanObject,
    mut v___y_5155_: *mut crate::leanh::LeanObject,
    mut v___y_5156_: *mut crate::leanh::LeanObject,
    mut v___y_5157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: u8 = 0;
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5179_: u8 = 0;
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5183_: u8 = 0;
    let mut v_a_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5187_: u8 = 0;
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_5150_) == 0 {
                    crate::leanh::lean_dec_ref(v_header_5149_);
                    crate::leanh::lean_dec(v_auxFunName_5148_);
                    crate::leanh::lean_dec_ref(v_indVal_5147_);
                    v___x_5159_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5159_, 0, v_b_5151_);
                    return v___x_5159_;
                } else {
                    v_head_5160_ = crate::leanh::lean_ctor_get(v_as_x27_5150_, 0);
                    v_tail_5161_ = crate::leanh::lean_ctor_get(v_as_x27_5150_, 1);
                    crate::leanh::lean_inc(v_head_5160_);
                    v___x_5162_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(v_head_5160_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_);
                    if crate::leanh::lean_obj_tag(v___x_5162_) == 0 {
                        v_a_5163_ = crate::leanh::lean_ctor_get(v___x_5162_, 0);
                        crate::leanh::lean_inc(v_a_5163_);
                        crate::leanh::lean_dec_ref_known(v___x_5162_, 1);
                        v_toConstantVal_5164_ = crate::leanh::lean_ctor_get(v_a_5163_, 0);
                        crate::leanh::lean_inc_ref(v_toConstantVal_5164_);
                        crate::leanh::lean_dec(v_a_5163_);
                        v_name_5165_ = crate::leanh::lean_ctor_get(v_toConstantVal_5164_, 0);
                        crate::leanh::lean_inc(v_name_5165_);
                        v_type_5166_ = crate::leanh::lean_ctor_get(v_toConstantVal_5164_, 2);
                        crate::leanh::lean_inc_ref(v_type_5166_);
                        crate::leanh::lean_dec_ref(v_toConstantVal_5164_);
                        v___f_5167_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__0;
                        v___x_5168_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_alts_5169_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1;
                        crate::leanh::lean_inc(v_head_5160_);
                        crate::leanh::lean_inc_ref(v_header_5149_);
                        crate::leanh::lean_inc(v_auxFunName_5148_);
                        crate::leanh::lean_inc_ref(v_indVal_5147_);
                        v___f_5170_ = crate::leanh::lean_alloc_closure(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___boxed as *mut core::ffi::c_void, 17, 8);
                        crate::leanh::lean_closure_set(v___f_5170_, 0, v_indVal_5147_);
                        crate::leanh::lean_closure_set(v___f_5170_, 1, v___x_5168_);
                        crate::leanh::lean_closure_set(v___f_5170_, 2, v_alts_5169_);
                        crate::leanh::lean_closure_set(v___f_5170_, 3, v_name_5165_);
                        crate::leanh::lean_closure_set(v___f_5170_, 4, v_auxFunName_5148_);
                        crate::leanh::lean_closure_set(v___f_5170_, 5, v_header_5149_);
                        crate::leanh::lean_closure_set(v___f_5170_, 6, v___f_5167_);
                        crate::leanh::lean_closure_set(v___f_5170_, 7, v_head_5160_);
                        v___x_5171_ = 0;
                        v___x_5172_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(v_type_5166_, v___f_5170_, v___x_5171_, v___x_5171_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_);
                        if crate::leanh::lean_obj_tag(v___x_5172_) == 0 {
                            v_a_5173_ = crate::leanh::lean_ctor_get(v___x_5172_, 0);
                            crate::leanh::lean_inc(v_a_5173_);
                            crate::leanh::lean_dec_ref_known(v___x_5172_, 1);
                            v___x_5174_ = lean_array_push(v_b_5151_, v_a_5173_);
                            v_as_x27_5150_ = v_tail_5161_;
                            v_b_5151_ = v___x_5174_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_b_5151_);
                            crate::leanh::lean_dec_ref(v_header_5149_);
                            crate::leanh::lean_dec(v_auxFunName_5148_);
                            crate::leanh::lean_dec_ref(v_indVal_5147_);
                            v_a_5176_ = crate::leanh::lean_ctor_get(v___x_5172_, 0);
                            v_isSharedCheck_5183_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5172_)) as u8;
                            if v_isSharedCheck_5183_ == 0 {
                                v___x_5178_ = v___x_5172_;
                                v_isShared_5179_ = v_isSharedCheck_5183_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5176_);
                                crate::leanh::lean_dec(v___x_5172_);
                                v___x_5178_ = crate::leanh::lean_box(0);
                                v_isShared_5179_ = v_isSharedCheck_5183_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_5151_);
                        crate::leanh::lean_dec_ref(v_header_5149_);
                        crate::leanh::lean_dec(v_auxFunName_5148_);
                        crate::leanh::lean_dec_ref(v_indVal_5147_);
                        v_a_5184_ = crate::leanh::lean_ctor_get(v___x_5162_, 0);
                        v_isSharedCheck_5191_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5162_)) as u8;
                        if v_isSharedCheck_5191_ == 0 {
                            v___x_5186_ = v___x_5162_;
                            v_isShared_5187_ = v_isSharedCheck_5191_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5184_);
                            crate::leanh::lean_dec(v___x_5162_);
                            v___x_5186_ = crate::leanh::lean_box(0);
                            v_isShared_5187_ = v_isSharedCheck_5191_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5179_ == 0 {
                    v___x_5181_ = v___x_5178_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5182_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5182_, 0, v_a_5176_);
                    v___x_5181_ = v_reuseFailAlloc_5182_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5181_;
            }
            3 => {
                if v_isShared_5187_ == 0 {
                    v___x_5189_ = v___x_5186_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5190_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5190_, 0, v_a_5184_);
                    v___x_5189_ = v_reuseFailAlloc_5190_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___boxed(
    mut v_indVal_5192_: *mut crate::leanh::LeanObject,
    mut v_auxFunName_5193_: *mut crate::leanh::LeanObject,
    mut v_header_5194_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5195_: *mut crate::leanh::LeanObject,
    mut v_b_5196_: *mut crate::leanh::LeanObject,
    mut v___y_5197_: *mut crate::leanh::LeanObject,
    mut v___y_5198_: *mut crate::leanh::LeanObject,
    mut v___y_5199_: *mut crate::leanh::LeanObject,
    mut v___y_5200_: *mut crate::leanh::LeanObject,
    mut v___y_5201_: *mut crate::leanh::LeanObject,
    mut v___y_5202_: *mut crate::leanh::LeanObject,
    mut v___y_5203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5204_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(v_indVal_5192_, v_auxFunName_5193_, v_header_5194_, v_as_x27_5195_, v_b_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_);
    crate::leanh::lean_dec(v___y_5202_);
    crate::leanh::lean_dec_ref(v___y_5201_);
    crate::leanh::lean_dec(v___y_5200_);
    crate::leanh::lean_dec_ref(v___y_5199_);
    crate::leanh::lean_dec(v___y_5198_);
    crate::leanh::lean_dec_ref(v___y_5197_);
    crate::leanh::lean_dec(v_as_x27_5195_);
    return v_res_5204_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(
    mut v_sz_5205_: usize,
    mut v_i_5206_: usize,
    mut v_bs_5207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5208_: u8 = 0;
    let mut v_v_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: usize = 0;
    let mut v___x_5213_: usize = 0;
    let mut v___x_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5208_ = lean_usize_dec_lt(v_i_5206_, v_sz_5205_);
                if v___x_5208_ == 0 {
                    return v_bs_5207_;
                } else {
                    v_v_5209_ = lean_array_uget(v_bs_5207_, v_i_5206_);
                    v___x_5210_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5211_ = lean_array_uset(v_bs_5207_, v_i_5206_, v___x_5210_);
                    v___x_5212_ = 1usize;
                    v___x_5213_ = lean_usize_add(v_i_5206_, v___x_5212_);
                    v___x_5214_ = lean_array_uset(v_bs_x27_5211_, v_i_5206_, v_v_5209_);
                    v_i_5206_ = v___x_5213_;
                    v_bs_5207_ = v___x_5214_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4___boxed(
    mut v_sz_5216_: *mut crate::leanh::LeanObject,
    mut v_i_5217_: *mut crate::leanh::LeanObject,
    mut v_bs_5218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5219_: usize = 0;
    let mut v_i_boxed_5220_: usize = 0;
    let mut v_res_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5219_ = crate::leanh::lean_unbox_usize(v_sz_5216_);
    crate::leanh::lean_dec(v_sz_5216_);
    v_i_boxed_5220_ = crate::leanh::lean_unbox_usize(v_i_5217_);
    crate::leanh::lean_dec(v_i_5217_);
    v_res_5221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(v_sz_boxed_5219_, v_i_boxed_5220_, v_bs_5218_);
    return v_res_5221_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(
    mut v_header_5222_: *mut crate::leanh::LeanObject,
    mut v_indVal_5223_: *mut crate::leanh::LeanObject,
    mut v_auxFunName_5224_: *mut crate::leanh::LeanObject,
    mut v_a_5225_: *mut crate::leanh::LeanObject,
    mut v_a_5226_: *mut crate::leanh::LeanObject,
    mut v_a_5227_: *mut crate::leanh::LeanObject,
    mut v_a_5228_: *mut crate::leanh::LeanObject,
    mut v_a_5229_: *mut crate::leanh::LeanObject,
    mut v_a_5230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ctors_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5238_: u8 = 0;
    let mut v_sz_5239_: usize = 0;
    let mut v___x_5240_: usize = 0;
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5245_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ctors_5232_ = crate::leanh::lean_ctor_get(v_indVal_5223_, 4);
                crate::leanh::lean_inc(v_ctors_5232_);
                v_alts_5233_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1;
                v___x_5234_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(v_indVal_5223_, v_auxFunName_5224_, v_header_5222_, v_ctors_5232_, v_alts_5233_, v_a_5225_, v_a_5226_, v_a_5227_, v_a_5228_, v_a_5229_, v_a_5230_);
                crate::leanh::lean_dec(v_ctors_5232_);
                if crate::leanh::lean_obj_tag(v___x_5234_) == 0 {
                    v_a_5235_ = crate::leanh::lean_ctor_get(v___x_5234_, 0);
                    v_isSharedCheck_5245_ = (!crate::leanh::lean_is_exclusive(v___x_5234_)) as u8;
                    if v_isSharedCheck_5245_ == 0 {
                        v___x_5237_ = v___x_5234_;
                        v_isShared_5238_ = v_isSharedCheck_5245_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5235_);
                        crate::leanh::lean_dec(v___x_5234_);
                        v___x_5237_ = crate::leanh::lean_box(0);
                        v_isShared_5238_ = v_isSharedCheck_5245_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_5234_;
                }
            }
            1 => {
                v_sz_5239_ = lean_array_size(v_a_5235_);
                v___x_5240_ = 0usize;
                v___x_5241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(v_sz_5239_, v___x_5240_, v_a_5235_);
                if v_isShared_5238_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5237_, 0, v___x_5241_);
                    v___x_5243_ = v___x_5237_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5244_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5244_, 0, v___x_5241_);
                    v___x_5243_ = v_reuseFailAlloc_5244_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5243_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts___boxed(
    mut v_header_5246_: *mut crate::leanh::LeanObject,
    mut v_indVal_5247_: *mut crate::leanh::LeanObject,
    mut v_auxFunName_5248_: *mut crate::leanh::LeanObject,
    mut v_a_5249_: *mut crate::leanh::LeanObject,
    mut v_a_5250_: *mut crate::leanh::LeanObject,
    mut v_a_5251_: *mut crate::leanh::LeanObject,
    mut v_a_5252_: *mut crate::leanh::LeanObject,
    mut v_a_5253_: *mut crate::leanh::LeanObject,
    mut v_a_5254_: *mut crate::leanh::LeanObject,
    mut v_a_5255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5256_ =
        l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(
            v_header_5246_,
            v_indVal_5247_,
            v_auxFunName_5248_,
            v_a_5249_,
            v_a_5250_,
            v_a_5251_,
            v_a_5252_,
            v_a_5253_,
            v_a_5254_,
        );
    crate::leanh::lean_dec(v_a_5254_);
    crate::leanh::lean_dec_ref(v_a_5253_);
    crate::leanh::lean_dec(v_a_5252_);
    crate::leanh::lean_dec_ref(v_a_5251_);
    crate::leanh::lean_dec(v_a_5250_);
    crate::leanh::lean_dec_ref(v_a_5249_);
    return v_res_5256_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1(
    mut v_upperBound_5257_: *mut crate::leanh::LeanObject,
    mut v_xs_5258_: *mut crate::leanh::LeanObject,
    mut v_indVal_5259_: *mut crate::leanh::LeanObject,
    mut v_auxFunName_5260_: *mut crate::leanh::LeanObject,
    mut v_header_5261_: *mut crate::leanh::LeanObject,
    mut v_inst_5262_: *mut crate::leanh::LeanObject,
    mut v_R_5263_: *mut crate::leanh::LeanObject,
    mut v_a_5264_: *mut crate::leanh::LeanObject,
    mut v_b_5265_: *mut crate::leanh::LeanObject,
    mut v_c_5266_: *mut crate::leanh::LeanObject,
    mut v___y_5267_: *mut crate::leanh::LeanObject,
    mut v___y_5268_: *mut crate::leanh::LeanObject,
    mut v___y_5269_: *mut crate::leanh::LeanObject,
    mut v___y_5270_: *mut crate::leanh::LeanObject,
    mut v___y_5271_: *mut crate::leanh::LeanObject,
    mut v___y_5272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5274_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(v_upperBound_5257_, v_xs_5258_, v_indVal_5259_, v_auxFunName_5260_, v_header_5261_, v_a_5264_, v_b_5265_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_);
    return v___x_5274_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_5275_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_xs_5276_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_indVal_5277_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_auxFunName_5278_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_header_5279_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_5280_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_R_5281_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_5282_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_b_5283_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_c_5284_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_5285_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_5286_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_5287_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5288_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5289_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5290_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5291_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5292_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1(v_upperBound_5275_, v_xs_5276_, v_indVal_5277_, v_auxFunName_5278_, v_header_5279_, v_inst_5280_, v_R_5281_, v_a_5282_, v_b_5283_, v_c_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_);
    crate::leanh::lean_dec(v___y_5290_);
    crate::leanh::lean_dec_ref(v___y_5289_);
    crate::leanh::lean_dec(v___y_5288_);
    crate::leanh::lean_dec_ref(v___y_5287_);
    crate::leanh::lean_dec(v___y_5286_);
    crate::leanh::lean_dec_ref(v___y_5285_);
    crate::leanh::lean_dec_ref(v_header_5279_);
    crate::leanh::lean_dec_ref(v_indVal_5277_);
    crate::leanh::lean_dec_ref(v_xs_5276_);
    crate::leanh::lean_dec(v_upperBound_5275_);
    return v_res_5292_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2(
    mut v_upperBound_5293_: *mut crate::leanh::LeanObject,
    mut v_inst_5294_: *mut crate::leanh::LeanObject,
    mut v_R_5295_: *mut crate::leanh::LeanObject,
    mut v_a_5296_: *mut crate::leanh::LeanObject,
    mut v_b_5297_: *mut crate::leanh::LeanObject,
    mut v_c_5298_: *mut crate::leanh::LeanObject,
    mut v___y_5299_: *mut crate::leanh::LeanObject,
    mut v___y_5300_: *mut crate::leanh::LeanObject,
    mut v___y_5301_: *mut crate::leanh::LeanObject,
    mut v___y_5302_: *mut crate::leanh::LeanObject,
    mut v___y_5303_: *mut crate::leanh::LeanObject,
    mut v___y_5304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5306_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(v_upperBound_5293_, v_a_5296_, v_b_5297_, v___y_5303_);
    return v___x_5306_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___boxed(
    mut v_upperBound_5307_: *mut crate::leanh::LeanObject,
    mut v_inst_5308_: *mut crate::leanh::LeanObject,
    mut v_R_5309_: *mut crate::leanh::LeanObject,
    mut v_a_5310_: *mut crate::leanh::LeanObject,
    mut v_b_5311_: *mut crate::leanh::LeanObject,
    mut v_c_5312_: *mut crate::leanh::LeanObject,
    mut v___y_5313_: *mut crate::leanh::LeanObject,
    mut v___y_5314_: *mut crate::leanh::LeanObject,
    mut v___y_5315_: *mut crate::leanh::LeanObject,
    mut v___y_5316_: *mut crate::leanh::LeanObject,
    mut v___y_5317_: *mut crate::leanh::LeanObject,
    mut v___y_5318_: *mut crate::leanh::LeanObject,
    mut v___y_5319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5320_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2(v_upperBound_5307_, v_inst_5308_, v_R_5309_, v_a_5310_, v_b_5311_, v_c_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_);
    crate::leanh::lean_dec(v___y_5318_);
    crate::leanh::lean_dec_ref(v___y_5317_);
    crate::leanh::lean_dec(v___y_5316_);
    crate::leanh::lean_dec_ref(v___y_5315_);
    crate::leanh::lean_dec(v___y_5314_);
    crate::leanh::lean_dec_ref(v___y_5313_);
    crate::leanh::lean_dec(v_upperBound_5307_);
    return v_res_5320_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3(
    mut v_indVal_5321_: *mut crate::leanh::LeanObject,
    mut v_auxFunName_5322_: *mut crate::leanh::LeanObject,
    mut v_header_5323_: *mut crate::leanh::LeanObject,
    mut v_as_5324_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5325_: *mut crate::leanh::LeanObject,
    mut v_b_5326_: *mut crate::leanh::LeanObject,
    mut v_a_5327_: *mut crate::leanh::LeanObject,
    mut v___y_5328_: *mut crate::leanh::LeanObject,
    mut v___y_5329_: *mut crate::leanh::LeanObject,
    mut v___y_5330_: *mut crate::leanh::LeanObject,
    mut v___y_5331_: *mut crate::leanh::LeanObject,
    mut v___y_5332_: *mut crate::leanh::LeanObject,
    mut v___y_5333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5335_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(v_indVal_5321_, v_auxFunName_5322_, v_header_5323_, v_as_x27_5325_, v_b_5326_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_);
    return v___x_5335_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___boxed(
    mut v_indVal_5336_: *mut crate::leanh::LeanObject,
    mut v_auxFunName_5337_: *mut crate::leanh::LeanObject,
    mut v_header_5338_: *mut crate::leanh::LeanObject,
    mut v_as_5339_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5340_: *mut crate::leanh::LeanObject,
    mut v_b_5341_: *mut crate::leanh::LeanObject,
    mut v_a_5342_: *mut crate::leanh::LeanObject,
    mut v___y_5343_: *mut crate::leanh::LeanObject,
    mut v___y_5344_: *mut crate::leanh::LeanObject,
    mut v___y_5345_: *mut crate::leanh::LeanObject,
    mut v___y_5346_: *mut crate::leanh::LeanObject,
    mut v___y_5347_: *mut crate::leanh::LeanObject,
    mut v___y_5348_: *mut crate::leanh::LeanObject,
    mut v___y_5349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5350_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3(v_indVal_5336_, v_auxFunName_5337_, v_header_5338_, v_as_5339_, v_as_x27_5340_, v_b_5341_, v_a_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_);
    crate::leanh::lean_dec(v___y_5348_);
    crate::leanh::lean_dec_ref(v___y_5347_);
    crate::leanh::lean_dec(v___y_5346_);
    crate::leanh::lean_dec_ref(v___y_5345_);
    crate::leanh::lean_dec(v___y_5344_);
    crate::leanh::lean_dec_ref(v___y_5343_);
    crate::leanh::lean_dec(v_as_x27_5340_);
    crate::leanh::lean_dec(v_as_5339_);
    return v_res_5350_;
}
pub unsafe fn l_Lean_Elab_Deriving_Repr_mkBodyForInduct(
    mut v_header_5364_: *mut crate::leanh::LeanObject,
    mut v_indVal_5365_: *mut crate::leanh::LeanObject,
    mut v_auxFunName_5366_: *mut crate::leanh::LeanObject,
    mut v_a_5367_: *mut crate::leanh::LeanObject,
    mut v_a_5368_: *mut crate::leanh::LeanObject,
    mut v_a_5369_: *mut crate::leanh::LeanObject,
    mut v_a_5370_: *mut crate::leanh::LeanObject,
    mut v_a_5371_: *mut crate::leanh::LeanObject,
    mut v_a_5372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5380_: u8 = 0;
    let mut v_ref_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: u8 = 0;
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5390_: usize = 0;
    let mut v___x_5391_: usize = 0;
    let mut v___x_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5407_: u8 = 0;
    let mut v_a_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5411_: u8 = 0;
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5415_: u8 = 0;
    let mut v_a_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5419_: u8 = 0;
    let mut v___x_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5423_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_indVal_5365_);
                crate::leanh::lean_inc_ref(v_header_5364_);
                v___x_5374_ = l_Lean_Elab_Deriving_mkDiscrs(
                    v_header_5364_,
                    v_indVal_5365_,
                    v_a_5367_,
                    v_a_5368_,
                    v_a_5369_,
                    v_a_5370_,
                    v_a_5371_,
                    v_a_5372_,
                );
                if crate::leanh::lean_obj_tag(v___x_5374_) == 0 {
                    v_a_5375_ = crate::leanh::lean_ctor_get(v___x_5374_, 0);
                    crate::leanh::lean_inc(v_a_5375_);
                    crate::leanh::lean_dec_ref_known(v___x_5374_, 1);
                    v___x_5376_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(v_header_5364_, v_indVal_5365_, v_auxFunName_5366_, v_a_5367_, v_a_5368_, v_a_5369_, v_a_5370_, v_a_5371_, v_a_5372_);
                    if crate::leanh::lean_obj_tag(v___x_5376_) == 0 {
                        v_a_5377_ = crate::leanh::lean_ctor_get(v___x_5376_, 0);
                        v_isSharedCheck_5407_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5376_)) as u8;
                        if v_isSharedCheck_5407_ == 0 {
                            v___x_5379_ = v___x_5376_;
                            v_isShared_5380_ = v_isSharedCheck_5407_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5377_);
                            crate::leanh::lean_dec(v___x_5376_);
                            v___x_5379_ = crate::leanh::lean_box(0);
                            v_isShared_5380_ = v_isSharedCheck_5407_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5375_);
                        v_a_5408_ = crate::leanh::lean_ctor_get(v___x_5376_, 0);
                        v_isSharedCheck_5415_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5376_)) as u8;
                        if v_isSharedCheck_5415_ == 0 {
                            v___x_5410_ = v___x_5376_;
                            v_isShared_5411_ = v_isSharedCheck_5415_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5408_);
                            crate::leanh::lean_dec(v___x_5376_);
                            v___x_5410_ = crate::leanh::lean_box(0);
                            v_isShared_5411_ = v_isSharedCheck_5415_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_auxFunName_5366_);
                    crate::leanh::lean_dec_ref(v_indVal_5365_);
                    crate::leanh::lean_dec_ref(v_header_5364_);
                    v_a_5416_ = crate::leanh::lean_ctor_get(v___x_5374_, 0);
                    v_isSharedCheck_5423_ = (!crate::leanh::lean_is_exclusive(v___x_5374_)) as u8;
                    if v_isSharedCheck_5423_ == 0 {
                        v___x_5418_ = v___x_5374_;
                        v_isShared_5419_ = v_isSharedCheck_5423_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5416_);
                        crate::leanh::lean_dec(v___x_5374_);
                        v___x_5418_ = crate::leanh::lean_box(0);
                        v_isShared_5419_ = v_isSharedCheck_5423_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_ref_5381_ = crate::leanh::lean_ctor_get(v_a_5371_, 5);
                v___x_5382_ = 0;
                v___x_5383_ = l_Lean_SourceInfo_fromRef(v_ref_5381_, v___x_5382_);
                v___x_5384_ = l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0;
                v___x_5385_ = l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1;
                crate::leanh::lean_inc_n(v___x_5383_, 6);
                v___x_5386_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5386_, 0, v___x_5383_);
                crate::leanh::lean_ctor_set(v___x_5386_, 1, v___x_5384_);
                v___x_5387_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9;
                v___x_5388_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once
                    ),
                    _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22,
                );
                v___x_5389_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5389_, 0, v___x_5383_);
                crate::leanh::lean_ctor_set(v___x_5389_, 1, v___x_5387_);
                crate::leanh::lean_ctor_set(v___x_5389_, 2, v___x_5388_);
                v_sz_5390_ = lean_array_size(v_a_5375_);
                v___x_5391_ = 0usize;
                v___x_5392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(v_sz_5390_, v___x_5391_, v_a_5375_);
                v___x_5393_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16);
                v___x_5394_ = l_Lean_mkSepArray(v___x_5392_, v___x_5393_);
                crate::leanh::lean_dec_ref(v___x_5392_);
                v___x_5395_ = l_Array_append___redArg(v___x_5388_, v___x_5394_);
                crate::leanh::lean_dec_ref(v___x_5394_);
                v___x_5396_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5396_, 0, v___x_5383_);
                crate::leanh::lean_ctor_set(v___x_5396_, 1, v___x_5387_);
                crate::leanh::lean_ctor_set(v___x_5396_, 2, v___x_5395_);
                v___x_5397_ = l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__2;
                v___x_5398_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5398_, 0, v___x_5383_);
                crate::leanh::lean_ctor_set(v___x_5398_, 1, v___x_5397_);
                v___x_5399_ = l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4;
                v___x_5400_ = l_Array_append___redArg(v___x_5388_, v_a_5377_);
                crate::leanh::lean_dec(v_a_5377_);
                v___x_5401_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5401_, 0, v___x_5383_);
                crate::leanh::lean_ctor_set(v___x_5401_, 1, v___x_5387_);
                crate::leanh::lean_ctor_set(v___x_5401_, 2, v___x_5400_);
                v___x_5402_ = l_Lean_Syntax_node1(v___x_5383_, v___x_5399_, v___x_5401_);
                crate::leanh::lean_inc_ref(v___x_5389_);
                v___x_5403_ = l_Lean_Syntax_node6(
                    v___x_5383_,
                    v___x_5385_,
                    v___x_5386_,
                    v___x_5389_,
                    v___x_5389_,
                    v___x_5396_,
                    v___x_5398_,
                    v___x_5402_,
                );
                if v_isShared_5380_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5379_, 0, v___x_5403_);
                    v___x_5405_ = v___x_5379_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5406_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5406_, 0, v___x_5403_);
                    v___x_5405_ = v_reuseFailAlloc_5406_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5405_;
            }
            3 => {
                if v_isShared_5411_ == 0 {
                    v___x_5413_ = v___x_5410_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5414_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_a_5408_);
                    v___x_5413_ = v_reuseFailAlloc_5414_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5413_;
            }
            5 => {
                if v_isShared_5419_ == 0 {
                    v___x_5421_ = v___x_5418_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5422_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5422_, 0, v_a_5416_);
                    v___x_5421_ = v_reuseFailAlloc_5422_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5421_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_Repr_mkBodyForInduct___boxed(
    mut v_header_5424_: *mut crate::leanh::LeanObject,
    mut v_indVal_5425_: *mut crate::leanh::LeanObject,
    mut v_auxFunName_5426_: *mut crate::leanh::LeanObject,
    mut v_a_5427_: *mut crate::leanh::LeanObject,
    mut v_a_5428_: *mut crate::leanh::LeanObject,
    mut v_a_5429_: *mut crate::leanh::LeanObject,
    mut v_a_5430_: *mut crate::leanh::LeanObject,
    mut v_a_5431_: *mut crate::leanh::LeanObject,
    mut v_a_5432_: *mut crate::leanh::LeanObject,
    mut v_a_5433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5434_ = l_Lean_Elab_Deriving_Repr_mkBodyForInduct(
        v_header_5424_,
        v_indVal_5425_,
        v_auxFunName_5426_,
        v_a_5427_,
        v_a_5428_,
        v_a_5429_,
        v_a_5430_,
        v_a_5431_,
        v_a_5432_,
    );
    crate::leanh::lean_dec(v_a_5432_);
    crate::leanh::lean_dec_ref(v_a_5431_);
    crate::leanh::lean_dec(v_a_5430_);
    crate::leanh::lean_dec_ref(v_a_5429_);
    crate::leanh::lean_dec(v_a_5428_);
    crate::leanh::lean_dec_ref(v_a_5427_);
    return v_res_5434_;
}
pub unsafe fn l_Lean_Elab_Deriving_Repr_mkBody(
    mut v_header_5435_: *mut crate::leanh::LeanObject,
    mut v_indVal_5436_: *mut crate::leanh::LeanObject,
    mut v_auxFunName_5437_: *mut crate::leanh::LeanObject,
    mut v_a_5438_: *mut crate::leanh::LeanObject,
    mut v_a_5439_: *mut crate::leanh::LeanObject,
    mut v_a_5440_: *mut crate::leanh::LeanObject,
    mut v_a_5441_: *mut crate::leanh::LeanObject,
    mut v_a_5442_: *mut crate::leanh::LeanObject,
    mut v_a_5443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: u8 = 0;
    v___x_5445_ = lean_st_ref_get(v_a_5443_);
    v_toConstantVal_5446_ = crate::leanh::lean_ctor_get(v_indVal_5436_, 0);
    v_env_5447_ = crate::leanh::lean_ctor_get(v___x_5445_, 0);
    crate::leanh::lean_inc_ref(v_env_5447_);
    crate::leanh::lean_dec(v___x_5445_);
    v_name_5448_ = crate::leanh::lean_ctor_get(v_toConstantVal_5446_, 0);
    crate::leanh::lean_inc(v_name_5448_);
    v___x_5449_ = l_Lean_isStructure(v_env_5447_, v_name_5448_);
    if v___x_5449_ == 0 {
        let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5450_ = l_Lean_Elab_Deriving_Repr_mkBodyForInduct(
            v_header_5435_,
            v_indVal_5436_,
            v_auxFunName_5437_,
            v_a_5438_,
            v_a_5439_,
            v_a_5440_,
            v_a_5441_,
            v_a_5442_,
            v_a_5443_,
        );
        return v___x_5450_;
    } else {
        let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_auxFunName_5437_);
        v___x_5451_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct(
            v_header_5435_,
            v_indVal_5436_,
            v_a_5438_,
            v_a_5439_,
            v_a_5440_,
            v_a_5441_,
            v_a_5442_,
            v_a_5443_,
        );
        crate::leanh::lean_dec_ref(v_header_5435_);
        return v___x_5451_;
    }
}
pub unsafe fn l_Lean_Elab_Deriving_Repr_mkBody___boxed(
    mut v_header_5452_: *mut crate::leanh::LeanObject,
    mut v_indVal_5453_: *mut crate::leanh::LeanObject,
    mut v_auxFunName_5454_: *mut crate::leanh::LeanObject,
    mut v_a_5455_: *mut crate::leanh::LeanObject,
    mut v_a_5456_: *mut crate::leanh::LeanObject,
    mut v_a_5457_: *mut crate::leanh::LeanObject,
    mut v_a_5458_: *mut crate::leanh::LeanObject,
    mut v_a_5459_: *mut crate::leanh::LeanObject,
    mut v_a_5460_: *mut crate::leanh::LeanObject,
    mut v_a_5461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5462_ = l_Lean_Elab_Deriving_Repr_mkBody(
        v_header_5452_,
        v_indVal_5453_,
        v_auxFunName_5454_,
        v_a_5455_,
        v_a_5456_,
        v_a_5457_,
        v_a_5458_,
        v_a_5459_,
        v_a_5460_,
    );
    crate::leanh::lean_dec(v_a_5460_);
    crate::leanh::lean_dec_ref(v_a_5459_);
    crate::leanh::lean_dec(v_a_5458_);
    crate::leanh::lean_dec_ref(v_a_5457_);
    crate::leanh::lean_dec(v_a_5456_);
    crate::leanh::lean_dec_ref(v_a_5455_);
    return v_res_5462_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5503_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15;
    v___x_5504_ = l_String_toRawSubstring_x27(v___x_5503_);
    return v___x_5504_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5533_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36;
    v___x_5534_ = l_String_toRawSubstring_x27(v___x_5533_);
    return v___x_5534_;
}
pub unsafe fn l_Lean_Elab_Deriving_Repr_mkAuxFunction(
    mut v_ctx_5571_: *mut crate::leanh::LeanObject,
    mut v_i_5572_: *mut crate::leanh::LeanObject,
    mut v_a_5573_: *mut crate::leanh::LeanObject,
    mut v_a_5574_: *mut crate::leanh::LeanObject,
    mut v_a_5575_: *mut crate::leanh::LeanObject,
    mut v_a_5576_: *mut crate::leanh::LeanObject,
    mut v_a_5577_: *mut crate::leanh::LeanObject,
    mut v_a_5578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_typeInfos_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxFunNames_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usePartial_5582_: u8 = 0;
    let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indVal_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5589_: u8 = 0;
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxFunName_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binders_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5598_: u8 = 0;
    let mut v_ref_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5661_: u8 = 0;
    let mut v_unused_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binders_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5668_: u8 = 0;
    let mut v_ref_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: u8 = 0;
    let mut v___x_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5737_: u8 = 0;
    let mut v_unused_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_argNames_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5753_: u8 = 0;
    let mut v___x_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5757_: u8 = 0;
    let mut v_isSharedCheck_5758_: u8 = 0;
    let mut v_a_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5762_: u8 = 0;
    let mut v___x_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5766_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_typeInfos_5580_ = crate::leanh::lean_ctor_get(v_ctx_5571_, 1);
                v_auxFunNames_5581_ = crate::leanh::lean_ctor_get(v_ctx_5571_, 2);
                v_usePartial_5582_ = crate::leanh::lean_ctor_get_uint8(
                    v_ctx_5571_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v___x_5583_ = l_Lean_instInhabitedInductiveVal_default;
                v_indVal_5584_ = lean_array_get_borrowed(v___x_5583_, v_typeInfos_5580_, v_i_5572_);
                crate::leanh::lean_inc(v_indVal_5584_);
                v___x_5585_ = l_Lean_Elab_Deriving_Repr_mkReprHeader(
                    v_indVal_5584_,
                    v_a_5573_,
                    v_a_5574_,
                    v_a_5575_,
                    v_a_5576_,
                    v_a_5577_,
                    v_a_5578_,
                );
                if crate::leanh::lean_obj_tag(v___x_5585_) == 0 {
                    v_a_5586_ = crate::leanh::lean_ctor_get(v___x_5585_, 0);
                    v_isSharedCheck_5758_ = (!crate::leanh::lean_is_exclusive(v___x_5585_)) as u8;
                    if v_isSharedCheck_5758_ == 0 {
                        v___x_5588_ = v___x_5585_;
                        v_isShared_5589_ = v_isSharedCheck_5758_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5586_);
                        crate::leanh::lean_dec(v___x_5585_);
                        v___x_5588_ = crate::leanh::lean_box(0);
                        v_isShared_5589_ = v_isSharedCheck_5758_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5759_ = crate::leanh::lean_ctor_get(v___x_5585_, 0);
                    v_isSharedCheck_5766_ = (!crate::leanh::lean_is_exclusive(v___x_5585_)) as u8;
                    if v_isSharedCheck_5766_ == 0 {
                        v___x_5761_ = v___x_5585_;
                        v_isShared_5762_ = v_isSharedCheck_5766_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5759_);
                        crate::leanh::lean_dec(v___x_5585_);
                        v___x_5761_ = crate::leanh::lean_box(0);
                        v_isShared_5762_ = v_isSharedCheck_5766_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5590_ = crate::leanh::lean_box(0);
                v_auxFunName_5591_ =
                    lean_array_get_borrowed(v___x_5590_, v_auxFunNames_5581_, v_i_5572_);
                crate::leanh::lean_inc(v_auxFunName_5591_);
                crate::leanh::lean_inc(v_indVal_5584_);
                crate::leanh::lean_inc(v_a_5586_);
                v___x_5741_ = l_Lean_Elab_Deriving_Repr_mkBody(
                    v_a_5586_,
                    v_indVal_5584_,
                    v_auxFunName_5591_,
                    v_a_5573_,
                    v_a_5574_,
                    v_a_5575_,
                    v_a_5576_,
                    v_a_5577_,
                    v_a_5578_,
                );
                if crate::leanh::lean_obj_tag(v___x_5741_) == 0 {
                    if v_usePartial_5582_ == 0 {
                        v_a_5742_ = crate::leanh::lean_ctor_get(v___x_5741_, 0);
                        crate::leanh::lean_inc(v_a_5742_);
                        crate::leanh::lean_dec_ref_known(v___x_5741_, 1);
                        v_body_5593_ = v_a_5742_;
                        v___y_5594_ = v_a_5577_;
                        state = 2;
                        continue;
                    } else {
                        v_a_5743_ = crate::leanh::lean_ctor_get(v___x_5741_, 0);
                        crate::leanh::lean_inc(v_a_5743_);
                        crate::leanh::lean_dec_ref_known(v___x_5741_, 1);
                        v_argNames_5744_ = crate::leanh::lean_ctor_get(v_a_5586_, 1);
                        v___x_5745_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1;
                        crate::leanh::lean_inc_ref(v_argNames_5744_);
                        v___x_5746_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(
                            v_ctx_5571_,
                            v___x_5745_,
                            v_argNames_5744_,
                            v_a_5573_,
                            v_a_5574_,
                            v_a_5575_,
                            v_a_5576_,
                            v_a_5577_,
                            v_a_5578_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5746_) == 0 {
                            v_a_5747_ = crate::leanh::lean_ctor_get(v___x_5746_, 0);
                            crate::leanh::lean_inc(v_a_5747_);
                            crate::leanh::lean_dec_ref_known(v___x_5746_, 1);
                            v___x_5748_ = l_Lean_Elab_Deriving_mkLet(
                                v_a_5747_, v_a_5743_, v_a_5573_, v_a_5574_, v_a_5575_, v_a_5576_,
                                v_a_5577_, v_a_5578_,
                            );
                            crate::leanh::lean_dec(v_a_5747_);
                            if crate::leanh::lean_obj_tag(v___x_5748_) == 0 {
                                v_a_5749_ = crate::leanh::lean_ctor_get(v___x_5748_, 0);
                                crate::leanh::lean_inc(v_a_5749_);
                                crate::leanh::lean_dec_ref_known(v___x_5748_, 1);
                                v_body_5593_ = v_a_5749_;
                                v___y_5594_ = v_a_5577_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_5588_);
                                crate::leanh::lean_dec(v_a_5586_);
                                return v___x_5748_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5743_);
                            crate::leanh::lean_del_object(v___x_5588_);
                            crate::leanh::lean_dec(v_a_5586_);
                            v_a_5750_ = crate::leanh::lean_ctor_get(v___x_5746_, 0);
                            v_isSharedCheck_5757_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5746_)) as u8;
                            if v_isSharedCheck_5757_ == 0 {
                                v___x_5752_ = v___x_5746_;
                                v_isShared_5753_ = v_isSharedCheck_5757_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5750_);
                                crate::leanh::lean_dec(v___x_5746_);
                                v___x_5752_ = crate::leanh::lean_box(0);
                                v_isShared_5753_ = v_isSharedCheck_5757_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5588_);
                    crate::leanh::lean_dec(v_a_5586_);
                    return v___x_5741_;
                }
            }
            2 => {
                if v_usePartial_5582_ == 0 {
                    v_binders_5595_ = crate::leanh::lean_ctor_get(v_a_5586_, 0);
                    v_isSharedCheck_5661_ = (!crate::leanh::lean_is_exclusive(v_a_5586_)) as u8;
                    if v_isSharedCheck_5661_ == 0 {
                        v_unused_5662_ = crate::leanh::lean_ctor_get(v_a_5586_, 3);
                        crate::leanh::lean_dec(v_unused_5662_);
                        v_unused_5663_ = crate::leanh::lean_ctor_get(v_a_5586_, 2);
                        crate::leanh::lean_dec(v_unused_5663_);
                        v_unused_5664_ = crate::leanh::lean_ctor_get(v_a_5586_, 1);
                        crate::leanh::lean_dec(v_unused_5664_);
                        v___x_5597_ = v_a_5586_;
                        v_isShared_5598_ = v_isSharedCheck_5661_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_binders_5595_);
                        crate::leanh::lean_dec(v_a_5586_);
                        v___x_5597_ = crate::leanh::lean_box(0);
                        v_isShared_5598_ = v_isSharedCheck_5661_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_binders_5665_ = crate::leanh::lean_ctor_get(v_a_5586_, 0);
                    v_isSharedCheck_5737_ = (!crate::leanh::lean_is_exclusive(v_a_5586_)) as u8;
                    if v_isSharedCheck_5737_ == 0 {
                        v_unused_5738_ = crate::leanh::lean_ctor_get(v_a_5586_, 3);
                        crate::leanh::lean_dec(v_unused_5738_);
                        v_unused_5739_ = crate::leanh::lean_ctor_get(v_a_5586_, 2);
                        crate::leanh::lean_dec(v_unused_5739_);
                        v_unused_5740_ = crate::leanh::lean_ctor_get(v_a_5586_, 1);
                        crate::leanh::lean_dec(v_unused_5740_);
                        v___x_5667_ = v_a_5586_;
                        v_isShared_5668_ = v_isSharedCheck_5737_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_binders_5665_);
                        crate::leanh::lean_dec(v_a_5586_);
                        v___x_5667_ = crate::leanh::lean_box(0);
                        v_isShared_5668_ = v_isSharedCheck_5737_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v_ref_5599_ = crate::leanh::lean_ctor_get(v___y_5594_, 5);
                v_quotContext_5600_ = crate::leanh::lean_ctor_get(v___y_5594_, 10);
                v_currMacroScope_5601_ = crate::leanh::lean_ctor_get(v___y_5594_, 11);
                v___x_5602_ = l_Lean_SourceInfo_fromRef(v_ref_5599_, v_usePartial_5582_);
                v___x_5603_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2;
                v___x_5604_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4;
                v___x_5605_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9;
                v___x_5606_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once
                    ),
                    _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22,
                );
                crate::leanh::lean_inc_n(v___x_5602_, 4);
                v___x_5607_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5607_, 0, v___x_5602_);
                crate::leanh::lean_ctor_set(v___x_5607_, 1, v___x_5605_);
                crate::leanh::lean_ctor_set(v___x_5607_, 2, v___x_5606_);
                v___x_5608_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6;
                v___x_5609_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7;
                v___x_5610_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5610_, 0, v___x_5602_);
                crate::leanh::lean_ctor_set(v___x_5610_, 1, v___x_5609_);
                v___x_5611_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9;
                v___x_5612_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11;
                crate::leanh::lean_inc_ref(v___x_5607_);
                v___x_5613_ = l_Lean_Syntax_node1(v___x_5602_, v___x_5612_, v___x_5607_);
                v___x_5614_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14;
                v___x_5615_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16_once
                    ),
                    _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16,
                );
                v___x_5616_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17;
                crate::leanh::lean_inc(v_currMacroScope_5601_);
                crate::leanh::lean_inc(v_quotContext_5600_);
                v___x_5617_ =
                    l_Lean_addMacroScope(v_quotContext_5600_, v___x_5616_, v_currMacroScope_5601_);
                v___x_5618_ = crate::leanh::lean_box(0);
                if v_isShared_5598_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5597_, 3);
                    crate::leanh::lean_ctor_set(v___x_5597_, 3, v___x_5618_);
                    crate::leanh::lean_ctor_set(v___x_5597_, 2, v___x_5617_);
                    crate::leanh::lean_ctor_set(v___x_5597_, 1, v___x_5615_);
                    crate::leanh::lean_ctor_set(v___x_5597_, 0, v___x_5602_);
                    v___x_5620_ = v___x_5597_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5660_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5660_, 0, v___x_5602_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5660_, 1, v___x_5615_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5660_, 2, v___x_5617_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5660_, 3, v___x_5618_);
                    v___x_5620_ = v_reuseFailAlloc_5660_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref_n(v___x_5607_, 11);
                crate::leanh::lean_inc_n(v___x_5602_, 19);
                v___x_5621_ =
                    l_Lean_Syntax_node2(v___x_5602_, v___x_5614_, v___x_5620_, v___x_5607_);
                v___x_5622_ =
                    l_Lean_Syntax_node2(v___x_5602_, v___x_5611_, v___x_5613_, v___x_5621_);
                v___x_5623_ = l_Lean_Syntax_node1(v___x_5602_, v___x_5605_, v___x_5622_);
                v___x_5624_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18;
                v___x_5625_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5625_, 0, v___x_5602_);
                crate::leanh::lean_ctor_set(v___x_5625_, 1, v___x_5624_);
                v___x_5626_ = l_Lean_Syntax_node3(
                    v___x_5602_,
                    v___x_5608_,
                    v___x_5610_,
                    v___x_5623_,
                    v___x_5625_,
                );
                v___x_5627_ = l_Lean_Syntax_node1(v___x_5602_, v___x_5605_, v___x_5626_);
                v___x_5628_ = l_Lean_Syntax_node7(
                    v___x_5602_,
                    v___x_5604_,
                    v___x_5607_,
                    v___x_5627_,
                    v___x_5607_,
                    v___x_5607_,
                    v___x_5607_,
                    v___x_5607_,
                    v___x_5607_,
                );
                v___x_5629_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20;
                v___x_5630_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21;
                v___x_5631_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5631_, 0, v___x_5602_);
                crate::leanh::lean_ctor_set(v___x_5631_, 1, v___x_5630_);
                v___x_5632_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23;
                crate::leanh::lean_inc(v_auxFunName_5591_);
                v___x_5633_ = lean_mk_syntax_ident(v_auxFunName_5591_);
                v___x_5634_ =
                    l_Lean_Syntax_node2(v___x_5602_, v___x_5632_, v___x_5633_, v___x_5607_);
                v___x_5635_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25;
                v___x_5636_ = l_Array_append___redArg(v___x_5606_, v_binders_5595_);
                crate::leanh::lean_dec_ref(v_binders_5595_);
                v___x_5637_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5637_, 0, v___x_5602_);
                crate::leanh::lean_ctor_set(v___x_5637_, 1, v___x_5605_);
                crate::leanh::lean_ctor_set(v___x_5637_, 2, v___x_5636_);
                v___x_5638_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27;
                v___x_5639_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13;
                v___x_5640_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5640_, 0, v___x_5602_);
                crate::leanh::lean_ctor_set(v___x_5640_, 1, v___x_5639_);
                v___x_5641_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28_once
                    ),
                    _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28,
                );
                v___x_5642_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29;
                crate::leanh::lean_inc(v_currMacroScope_5601_);
                crate::leanh::lean_inc(v_quotContext_5600_);
                v___x_5643_ =
                    l_Lean_addMacroScope(v_quotContext_5600_, v___x_5642_, v_currMacroScope_5601_);
                v___x_5644_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34;
                v___x_5645_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5645_, 0, v___x_5602_);
                crate::leanh::lean_ctor_set(v___x_5645_, 1, v___x_5641_);
                crate::leanh::lean_ctor_set(v___x_5645_, 2, v___x_5643_);
                crate::leanh::lean_ctor_set(v___x_5645_, 3, v___x_5644_);
                v___x_5646_ =
                    l_Lean_Syntax_node2(v___x_5602_, v___x_5638_, v___x_5640_, v___x_5645_);
                v___x_5647_ = l_Lean_Syntax_node1(v___x_5602_, v___x_5605_, v___x_5646_);
                v___x_5648_ =
                    l_Lean_Syntax_node2(v___x_5602_, v___x_5635_, v___x_5637_, v___x_5647_);
                v___x_5649_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36;
                v___x_5650_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37;
                v___x_5651_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5651_, 0, v___x_5602_);
                crate::leanh::lean_ctor_set(v___x_5651_, 1, v___x_5650_);
                v___x_5652_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40;
                v___x_5653_ =
                    l_Lean_Syntax_node2(v___x_5602_, v___x_5652_, v___x_5607_, v___x_5607_);
                v___x_5654_ = l_Lean_Syntax_node4(
                    v___x_5602_,
                    v___x_5649_,
                    v___x_5651_,
                    v_body_5593_,
                    v___x_5653_,
                    v___x_5607_,
                );
                v___x_5655_ = l_Lean_Syntax_node5(
                    v___x_5602_,
                    v___x_5629_,
                    v___x_5631_,
                    v___x_5634_,
                    v___x_5648_,
                    v___x_5654_,
                    v___x_5607_,
                );
                v___x_5656_ =
                    l_Lean_Syntax_node2(v___x_5602_, v___x_5603_, v___x_5628_, v___x_5655_);
                if v_isShared_5589_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5588_, 0, v___x_5656_);
                    v___x_5658_ = v___x_5588_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5659_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5659_, 0, v___x_5656_);
                    v___x_5658_ = v_reuseFailAlloc_5659_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5658_;
            }
            6 => {
                v_ref_5669_ = crate::leanh::lean_ctor_get(v___y_5594_, 5);
                v_quotContext_5670_ = crate::leanh::lean_ctor_get(v___y_5594_, 10);
                v_currMacroScope_5671_ = crate::leanh::lean_ctor_get(v___y_5594_, 11);
                v___x_5672_ = 0;
                v___x_5673_ = l_Lean_SourceInfo_fromRef(v_ref_5669_, v___x_5672_);
                v___x_5674_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2;
                v___x_5675_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4;
                v___x_5676_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9;
                v___x_5677_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once
                    ),
                    _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22,
                );
                crate::leanh::lean_inc_n(v___x_5673_, 4);
                v___x_5678_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5678_, 0, v___x_5673_);
                crate::leanh::lean_ctor_set(v___x_5678_, 1, v___x_5676_);
                crate::leanh::lean_ctor_set(v___x_5678_, 2, v___x_5677_);
                v___x_5679_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6;
                v___x_5680_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7;
                v___x_5681_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5681_, 0, v___x_5673_);
                crate::leanh::lean_ctor_set(v___x_5681_, 1, v___x_5680_);
                v___x_5682_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9;
                v___x_5683_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11;
                crate::leanh::lean_inc_ref(v___x_5678_);
                v___x_5684_ = l_Lean_Syntax_node1(v___x_5673_, v___x_5683_, v___x_5678_);
                v___x_5685_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14;
                v___x_5686_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16_once
                    ),
                    _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16,
                );
                v___x_5687_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17;
                crate::leanh::lean_inc(v_currMacroScope_5671_);
                crate::leanh::lean_inc(v_quotContext_5670_);
                v___x_5688_ =
                    l_Lean_addMacroScope(v_quotContext_5670_, v___x_5687_, v_currMacroScope_5671_);
                v___x_5689_ = crate::leanh::lean_box(0);
                if v_isShared_5668_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5667_, 3);
                    crate::leanh::lean_ctor_set(v___x_5667_, 3, v___x_5689_);
                    crate::leanh::lean_ctor_set(v___x_5667_, 2, v___x_5688_);
                    crate::leanh::lean_ctor_set(v___x_5667_, 1, v___x_5686_);
                    crate::leanh::lean_ctor_set(v___x_5667_, 0, v___x_5673_);
                    v___x_5691_ = v___x_5667_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5736_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5736_, 0, v___x_5673_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5736_, 1, v___x_5686_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5736_, 2, v___x_5688_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5736_, 3, v___x_5689_);
                    v___x_5691_ = v_reuseFailAlloc_5736_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_inc_ref_n(v___x_5678_, 10);
                crate::leanh::lean_inc_n(v___x_5673_, 22);
                v___x_5692_ =
                    l_Lean_Syntax_node2(v___x_5673_, v___x_5685_, v___x_5691_, v___x_5678_);
                v___x_5693_ =
                    l_Lean_Syntax_node2(v___x_5673_, v___x_5682_, v___x_5684_, v___x_5692_);
                v___x_5694_ = l_Lean_Syntax_node1(v___x_5673_, v___x_5676_, v___x_5693_);
                v___x_5695_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18;
                v___x_5696_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5696_, 0, v___x_5673_);
                crate::leanh::lean_ctor_set(v___x_5696_, 1, v___x_5695_);
                v___x_5697_ = l_Lean_Syntax_node3(
                    v___x_5673_,
                    v___x_5679_,
                    v___x_5681_,
                    v___x_5694_,
                    v___x_5696_,
                );
                v___x_5698_ = l_Lean_Syntax_node1(v___x_5673_, v___x_5676_, v___x_5697_);
                v___x_5699_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41;
                v___x_5700_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42;
                v___x_5701_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5701_, 0, v___x_5673_);
                crate::leanh::lean_ctor_set(v___x_5701_, 1, v___x_5699_);
                v___x_5702_ = l_Lean_Syntax_node1(v___x_5673_, v___x_5700_, v___x_5701_);
                v___x_5703_ = l_Lean_Syntax_node1(v___x_5673_, v___x_5676_, v___x_5702_);
                v___x_5704_ = l_Lean_Syntax_node7(
                    v___x_5673_,
                    v___x_5675_,
                    v___x_5678_,
                    v___x_5698_,
                    v___x_5678_,
                    v___x_5678_,
                    v___x_5678_,
                    v___x_5678_,
                    v___x_5703_,
                );
                v___x_5705_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20;
                v___x_5706_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21;
                v___x_5707_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5707_, 0, v___x_5673_);
                crate::leanh::lean_ctor_set(v___x_5707_, 1, v___x_5706_);
                v___x_5708_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23;
                crate::leanh::lean_inc(v_auxFunName_5591_);
                v___x_5709_ = lean_mk_syntax_ident(v_auxFunName_5591_);
                v___x_5710_ =
                    l_Lean_Syntax_node2(v___x_5673_, v___x_5708_, v___x_5709_, v___x_5678_);
                v___x_5711_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25;
                v___x_5712_ = l_Array_append___redArg(v___x_5677_, v_binders_5665_);
                crate::leanh::lean_dec_ref(v_binders_5665_);
                v___x_5713_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5713_, 0, v___x_5673_);
                crate::leanh::lean_ctor_set(v___x_5713_, 1, v___x_5676_);
                crate::leanh::lean_ctor_set(v___x_5713_, 2, v___x_5712_);
                v___x_5714_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27;
                v___x_5715_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13;
                v___x_5716_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5716_, 0, v___x_5673_);
                crate::leanh::lean_ctor_set(v___x_5716_, 1, v___x_5715_);
                v___x_5717_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28_once
                    ),
                    _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28,
                );
                v___x_5718_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29;
                crate::leanh::lean_inc(v_currMacroScope_5671_);
                crate::leanh::lean_inc(v_quotContext_5670_);
                v___x_5719_ =
                    l_Lean_addMacroScope(v_quotContext_5670_, v___x_5718_, v_currMacroScope_5671_);
                v___x_5720_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34;
                v___x_5721_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5721_, 0, v___x_5673_);
                crate::leanh::lean_ctor_set(v___x_5721_, 1, v___x_5717_);
                crate::leanh::lean_ctor_set(v___x_5721_, 2, v___x_5719_);
                crate::leanh::lean_ctor_set(v___x_5721_, 3, v___x_5720_);
                v___x_5722_ =
                    l_Lean_Syntax_node2(v___x_5673_, v___x_5714_, v___x_5716_, v___x_5721_);
                v___x_5723_ = l_Lean_Syntax_node1(v___x_5673_, v___x_5676_, v___x_5722_);
                v___x_5724_ =
                    l_Lean_Syntax_node2(v___x_5673_, v___x_5711_, v___x_5713_, v___x_5723_);
                v___x_5725_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36;
                v___x_5726_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37;
                v___x_5727_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5727_, 0, v___x_5673_);
                crate::leanh::lean_ctor_set(v___x_5727_, 1, v___x_5726_);
                v___x_5728_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40;
                v___x_5729_ =
                    l_Lean_Syntax_node2(v___x_5673_, v___x_5728_, v___x_5678_, v___x_5678_);
                v___x_5730_ = l_Lean_Syntax_node4(
                    v___x_5673_,
                    v___x_5725_,
                    v___x_5727_,
                    v_body_5593_,
                    v___x_5729_,
                    v___x_5678_,
                );
                v___x_5731_ = l_Lean_Syntax_node5(
                    v___x_5673_,
                    v___x_5705_,
                    v___x_5707_,
                    v___x_5710_,
                    v___x_5724_,
                    v___x_5730_,
                    v___x_5678_,
                );
                v___x_5732_ =
                    l_Lean_Syntax_node2(v___x_5673_, v___x_5674_, v___x_5704_, v___x_5731_);
                if v_isShared_5589_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5588_, 0, v___x_5732_);
                    v___x_5734_ = v___x_5588_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5735_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5735_, 0, v___x_5732_);
                    v___x_5734_ = v_reuseFailAlloc_5735_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5734_;
            }
            9 => {
                if v_isShared_5753_ == 0 {
                    v___x_5755_ = v___x_5752_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5756_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5756_, 0, v_a_5750_);
                    v___x_5755_ = v_reuseFailAlloc_5756_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5755_;
            }
            11 => {
                if v_isShared_5762_ == 0 {
                    v___x_5764_ = v___x_5761_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5765_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5765_, 0, v_a_5759_);
                    v___x_5764_ = v_reuseFailAlloc_5765_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_Repr_mkAuxFunction___boxed(
    mut v_ctx_5767_: *mut crate::leanh::LeanObject,
    mut v_i_5768_: *mut crate::leanh::LeanObject,
    mut v_a_5769_: *mut crate::leanh::LeanObject,
    mut v_a_5770_: *mut crate::leanh::LeanObject,
    mut v_a_5771_: *mut crate::leanh::LeanObject,
    mut v_a_5772_: *mut crate::leanh::LeanObject,
    mut v_a_5773_: *mut crate::leanh::LeanObject,
    mut v_a_5774_: *mut crate::leanh::LeanObject,
    mut v_a_5775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5776_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction(
        v_ctx_5767_,
        v_i_5768_,
        v_a_5769_,
        v_a_5770_,
        v_a_5771_,
        v_a_5772_,
        v_a_5773_,
        v_a_5774_,
    );
    crate::leanh::lean_dec(v_a_5774_);
    crate::leanh::lean_dec_ref(v_a_5773_);
    crate::leanh::lean_dec(v_a_5772_);
    crate::leanh::lean_dec_ref(v_a_5771_);
    crate::leanh::lean_dec(v_a_5770_);
    crate::leanh::lean_dec_ref(v_a_5769_);
    crate::leanh::lean_dec(v_i_5768_);
    crate::leanh::lean_dec_ref(v_ctx_5767_);
    return v_res_5776_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(
    mut v_upperBound_5777_: *mut crate::leanh::LeanObject,
    mut v_ctx_5778_: *mut crate::leanh::LeanObject,
    mut v_a_5779_: *mut crate::leanh::LeanObject,
    mut v_b_5780_: *mut crate::leanh::LeanObject,
    mut v___y_5781_: *mut crate::leanh::LeanObject,
    mut v___y_5782_: *mut crate::leanh::LeanObject,
    mut v___y_5783_: *mut crate::leanh::LeanObject,
    mut v___y_5784_: *mut crate::leanh::LeanObject,
    mut v___y_5785_: *mut crate::leanh::LeanObject,
    mut v___y_5786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5788_: u8 = 0;
    let mut v___x_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5799_: u8 = 0;
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5803_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5788_ = lean_nat_dec_lt(v_a_5779_, v_upperBound_5777_);
                if v___x_5788_ == 0 {
                    crate::leanh::lean_dec(v_a_5779_);
                    v___x_5789_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5789_, 0, v_b_5780_);
                    return v___x_5789_;
                } else {
                    v___x_5790_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction(
                        v_ctx_5778_,
                        v_a_5779_,
                        v___y_5781_,
                        v___y_5782_,
                        v___y_5783_,
                        v___y_5784_,
                        v___y_5785_,
                        v___y_5786_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5790_) == 0 {
                        v_a_5791_ = crate::leanh::lean_ctor_get(v___x_5790_, 0);
                        crate::leanh::lean_inc(v_a_5791_);
                        crate::leanh::lean_dec_ref_known(v___x_5790_, 1);
                        v___x_5792_ = lean_array_push(v_b_5780_, v_a_5791_);
                        v___x_5793_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5794_ = lean_nat_add(v_a_5779_, v___x_5793_);
                        crate::leanh::lean_dec(v_a_5779_);
                        v_a_5779_ = v___x_5794_;
                        v_b_5780_ = v___x_5792_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_5780_);
                        crate::leanh::lean_dec(v_a_5779_);
                        v_a_5796_ = crate::leanh::lean_ctor_get(v___x_5790_, 0);
                        v_isSharedCheck_5803_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5790_)) as u8;
                        if v_isSharedCheck_5803_ == 0 {
                            v___x_5798_ = v___x_5790_;
                            v_isShared_5799_ = v_isSharedCheck_5803_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5796_);
                            crate::leanh::lean_dec(v___x_5790_);
                            v___x_5798_ = crate::leanh::lean_box(0);
                            v_isShared_5799_ = v_isSharedCheck_5803_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5799_ == 0 {
                    v___x_5801_ = v___x_5798_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5802_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5802_, 0, v_a_5796_);
                    v___x_5801_ = v_reuseFailAlloc_5802_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg___boxed(
    mut v_upperBound_5804_: *mut crate::leanh::LeanObject,
    mut v_ctx_5805_: *mut crate::leanh::LeanObject,
    mut v_a_5806_: *mut crate::leanh::LeanObject,
    mut v_b_5807_: *mut crate::leanh::LeanObject,
    mut v___y_5808_: *mut crate::leanh::LeanObject,
    mut v___y_5809_: *mut crate::leanh::LeanObject,
    mut v___y_5810_: *mut crate::leanh::LeanObject,
    mut v___y_5811_: *mut crate::leanh::LeanObject,
    mut v___y_5812_: *mut crate::leanh::LeanObject,
    mut v___y_5813_: *mut crate::leanh::LeanObject,
    mut v___y_5814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5815_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(v_upperBound_5804_, v_ctx_5805_, v_a_5806_, v_b_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_, v___y_5812_, v___y_5813_);
    crate::leanh::lean_dec(v___y_5813_);
    crate::leanh::lean_dec_ref(v___y_5812_);
    crate::leanh::lean_dec(v___y_5811_);
    crate::leanh::lean_dec_ref(v___y_5810_);
    crate::leanh::lean_dec(v___y_5809_);
    crate::leanh::lean_dec_ref(v___y_5808_);
    crate::leanh::lean_dec_ref(v_ctx_5805_);
    crate::leanh::lean_dec(v_upperBound_5804_);
    return v_res_5815_;
}
pub unsafe fn l_Lean_Elab_Deriving_Repr_mkMutualBlock(
    mut v_ctx_5823_: *mut crate::leanh::LeanObject,
    mut v_a_5824_: *mut crate::leanh::LeanObject,
    mut v_a_5825_: *mut crate::leanh::LeanObject,
    mut v_a_5826_: *mut crate::leanh::LeanObject,
    mut v_a_5827_: *mut crate::leanh::LeanObject,
    mut v_a_5828_: *mut crate::leanh::LeanObject,
    mut v_a_5829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_typeInfos_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDefs_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5839_: u8 = 0;
    let mut v_ref_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: u8 = 0;
    let mut v___x_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5856_: u8 = 0;
    let mut v_a_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5860_: u8 = 0;
    let mut v___x_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5864_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_typeInfos_5831_ = crate::leanh::lean_ctor_get(v_ctx_5823_, 1);
                v___x_5832_ = lean_array_get_size(v_typeInfos_5831_);
                v___x_5833_ = crate::leanh::lean_unsigned_to_nat(0);
                v_auxDefs_5834_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1;
                v___x_5835_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(v___x_5832_, v_ctx_5823_, v___x_5833_, v_auxDefs_5834_, v_a_5824_, v_a_5825_, v_a_5826_, v_a_5827_, v_a_5828_, v_a_5829_);
                if crate::leanh::lean_obj_tag(v___x_5835_) == 0 {
                    v_a_5836_ = crate::leanh::lean_ctor_get(v___x_5835_, 0);
                    v_isSharedCheck_5856_ = (!crate::leanh::lean_is_exclusive(v___x_5835_)) as u8;
                    if v_isSharedCheck_5856_ == 0 {
                        v___x_5838_ = v___x_5835_;
                        v_isShared_5839_ = v_isSharedCheck_5856_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5836_);
                        crate::leanh::lean_dec(v___x_5835_);
                        v___x_5838_ = crate::leanh::lean_box(0);
                        v_isShared_5839_ = v_isSharedCheck_5856_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5857_ = crate::leanh::lean_ctor_get(v___x_5835_, 0);
                    v_isSharedCheck_5864_ = (!crate::leanh::lean_is_exclusive(v___x_5835_)) as u8;
                    if v_isSharedCheck_5864_ == 0 {
                        v___x_5859_ = v___x_5835_;
                        v_isShared_5860_ = v_isSharedCheck_5864_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5857_);
                        crate::leanh::lean_dec(v___x_5835_);
                        v___x_5859_ = crate::leanh::lean_box(0);
                        v_isShared_5860_ = v_isSharedCheck_5864_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_ref_5840_ = crate::leanh::lean_ctor_get(v_a_5828_, 5);
                v___x_5841_ = 0;
                v___x_5842_ = l_Lean_SourceInfo_fromRef(v_ref_5840_, v___x_5841_);
                v___x_5843_ = l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0;
                v___x_5844_ = l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1;
                crate::leanh::lean_inc_n(v___x_5842_, 3);
                v___x_5845_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5845_, 0, v___x_5842_);
                crate::leanh::lean_ctor_set(v___x_5845_, 1, v___x_5843_);
                v___x_5846_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9;
                v___x_5847_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once
                    ),
                    _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22,
                );
                v___x_5848_ = l_Array_append___redArg(v___x_5847_, v_a_5836_);
                crate::leanh::lean_dec(v_a_5836_);
                v___x_5849_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5849_, 0, v___x_5842_);
                crate::leanh::lean_ctor_set(v___x_5849_, 1, v___x_5846_);
                crate::leanh::lean_ctor_set(v___x_5849_, 2, v___x_5848_);
                v___x_5850_ = l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__2;
                v___x_5851_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5851_, 0, v___x_5842_);
                crate::leanh::lean_ctor_set(v___x_5851_, 1, v___x_5850_);
                v___x_5852_ = l_Lean_Syntax_node3(
                    v___x_5842_,
                    v___x_5844_,
                    v___x_5845_,
                    v___x_5849_,
                    v___x_5851_,
                );
                if v_isShared_5839_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5838_, 0, v___x_5852_);
                    v___x_5854_ = v___x_5838_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5855_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5855_, 0, v___x_5852_);
                    v___x_5854_ = v_reuseFailAlloc_5855_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5854_;
            }
            3 => {
                if v_isShared_5860_ == 0 {
                    v___x_5862_ = v___x_5859_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5863_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5863_, 0, v_a_5857_);
                    v___x_5862_ = v_reuseFailAlloc_5863_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5862_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_Repr_mkMutualBlock___boxed(
    mut v_ctx_5865_: *mut crate::leanh::LeanObject,
    mut v_a_5866_: *mut crate::leanh::LeanObject,
    mut v_a_5867_: *mut crate::leanh::LeanObject,
    mut v_a_5868_: *mut crate::leanh::LeanObject,
    mut v_a_5869_: *mut crate::leanh::LeanObject,
    mut v_a_5870_: *mut crate::leanh::LeanObject,
    mut v_a_5871_: *mut crate::leanh::LeanObject,
    mut v_a_5872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5873_ = l_Lean_Elab_Deriving_Repr_mkMutualBlock(
        v_ctx_5865_,
        v_a_5866_,
        v_a_5867_,
        v_a_5868_,
        v_a_5869_,
        v_a_5870_,
        v_a_5871_,
    );
    crate::leanh::lean_dec(v_a_5871_);
    crate::leanh::lean_dec_ref(v_a_5870_);
    crate::leanh::lean_dec(v_a_5869_);
    crate::leanh::lean_dec_ref(v_a_5868_);
    crate::leanh::lean_dec(v_a_5867_);
    crate::leanh::lean_dec_ref(v_a_5866_);
    crate::leanh::lean_dec_ref(v_ctx_5865_);
    return v_res_5873_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0(
    mut v_upperBound_5874_: *mut crate::leanh::LeanObject,
    mut v_ctx_5875_: *mut crate::leanh::LeanObject,
    mut v_inst_5876_: *mut crate::leanh::LeanObject,
    mut v_R_5877_: *mut crate::leanh::LeanObject,
    mut v_a_5878_: *mut crate::leanh::LeanObject,
    mut v_b_5879_: *mut crate::leanh::LeanObject,
    mut v_c_5880_: *mut crate::leanh::LeanObject,
    mut v___y_5881_: *mut crate::leanh::LeanObject,
    mut v___y_5882_: *mut crate::leanh::LeanObject,
    mut v___y_5883_: *mut crate::leanh::LeanObject,
    mut v___y_5884_: *mut crate::leanh::LeanObject,
    mut v___y_5885_: *mut crate::leanh::LeanObject,
    mut v___y_5886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5888_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(v_upperBound_5874_, v_ctx_5875_, v_a_5878_, v_b_5879_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_, v___y_5885_, v___y_5886_);
    return v___x_5888_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___boxed(
    mut v_upperBound_5889_: *mut crate::leanh::LeanObject,
    mut v_ctx_5890_: *mut crate::leanh::LeanObject,
    mut v_inst_5891_: *mut crate::leanh::LeanObject,
    mut v_R_5892_: *mut crate::leanh::LeanObject,
    mut v_a_5893_: *mut crate::leanh::LeanObject,
    mut v_b_5894_: *mut crate::leanh::LeanObject,
    mut v_c_5895_: *mut crate::leanh::LeanObject,
    mut v___y_5896_: *mut crate::leanh::LeanObject,
    mut v___y_5897_: *mut crate::leanh::LeanObject,
    mut v___y_5898_: *mut crate::leanh::LeanObject,
    mut v___y_5899_: *mut crate::leanh::LeanObject,
    mut v___y_5900_: *mut crate::leanh::LeanObject,
    mut v___y_5901_: *mut crate::leanh::LeanObject,
    mut v___y_5902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5903_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0(
            v_upperBound_5889_,
            v_ctx_5890_,
            v_inst_5891_,
            v_R_5892_,
            v_a_5893_,
            v_b_5894_,
            v_c_5895_,
            v___y_5896_,
            v___y_5897_,
            v___y_5898_,
            v___y_5899_,
            v___y_5900_,
            v___y_5901_,
        );
    crate::leanh::lean_dec(v___y_5901_);
    crate::leanh::lean_dec_ref(v___y_5900_);
    crate::leanh::lean_dec(v___y_5899_);
    crate::leanh::lean_dec_ref(v___y_5898_);
    crate::leanh::lean_dec(v___y_5897_);
    crate::leanh::lean_dec_ref(v___y_5896_);
    crate::leanh::lean_dec_ref(v_ctx_5890_);
    crate::leanh::lean_dec(v_upperBound_5889_);
    return v_res_5903_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__0(
    mut v_a_5904_: *mut crate::leanh::LeanObject,
    mut v_a_5905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5911_: u8 = 0;
    let mut v___x_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5917_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5904_) == 0 {
                    v___x_5906_ = l_List_reverse___redArg(v_a_5905_);
                    return v___x_5906_;
                } else {
                    v_head_5907_ = crate::leanh::lean_ctor_get(v_a_5904_, 0);
                    v_tail_5908_ = crate::leanh::lean_ctor_get(v_a_5904_, 1);
                    v_isSharedCheck_5917_ = (!crate::leanh::lean_is_exclusive(v_a_5904_)) as u8;
                    if v_isSharedCheck_5917_ == 0 {
                        v___x_5910_ = v_a_5904_;
                        v_isShared_5911_ = v_isSharedCheck_5917_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5908_);
                        crate::leanh::lean_inc(v_head_5907_);
                        crate::leanh::lean_dec(v_a_5904_);
                        v___x_5910_ = crate::leanh::lean_box(0);
                        v_isShared_5911_ = v_isSharedCheck_5917_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5912_ = l_Lean_MessageData_ofSyntax(v_head_5907_);
                if v_isShared_5911_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5910_, 1, v_a_5905_);
                    crate::leanh::lean_ctor_set(v___x_5910_, 0, v___x_5912_);
                    v___x_5914_ = v___x_5910_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5916_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5916_, 0, v___x_5912_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5916_, 1, v_a_5905_);
                    v___x_5914_ = v_reuseFailAlloc_5916_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5904_ = v_tail_5908_;
                v_a_5905_ = v___x_5914_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0()
-> f64 {
    let mut v___x_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: f64 = 0.0;
    v___x_5918_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5919_ = lean_float_of_nat(v___x_5918_);
    return v___x_5919_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(
    mut v_cls_5922_: *mut crate::leanh::LeanObject,
    mut v_msg_5923_: *mut crate::leanh::LeanObject,
    mut v___y_5924_: *mut crate::leanh::LeanObject,
    mut v___y_5925_: *mut crate::leanh::LeanObject,
    mut v___y_5926_: *mut crate::leanh::LeanObject,
    mut v___y_5927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5934_: u8 = 0;
    let mut v___x_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5947_: u8 = 0;
    let mut v_tid_5948_: u64 = 0;
    let mut v_traces_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5952_: u8 = 0;
    let mut v___x_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: f64 = 0.0;
    let mut v___x_5955_: u8 = 0;
    let mut v___x_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5973_: u8 = 0;
    let mut v_isSharedCheck_5974_: u8 = 0;
    let mut v_isSharedCheck_5975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5929_ = crate::leanh::lean_ctor_get(v___y_5926_, 5);
                v___x_5930_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4(v_msg_5923_, v___y_5924_, v___y_5925_, v___y_5926_, v___y_5927_);
                v_a_5931_ = crate::leanh::lean_ctor_get(v___x_5930_, 0);
                v_isSharedCheck_5975_ = (!crate::leanh::lean_is_exclusive(v___x_5930_)) as u8;
                if v_isSharedCheck_5975_ == 0 {
                    v___x_5933_ = v___x_5930_;
                    v_isShared_5934_ = v_isSharedCheck_5975_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5931_);
                    crate::leanh::lean_dec(v___x_5930_);
                    v___x_5933_ = crate::leanh::lean_box(0);
                    v_isShared_5934_ = v_isSharedCheck_5975_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5935_ = lean_st_ref_take(v___y_5927_);
                v_traceState_5936_ = crate::leanh::lean_ctor_get(v___x_5935_, 4);
                v_env_5937_ = crate::leanh::lean_ctor_get(v___x_5935_, 0);
                v_nextMacroScope_5938_ = crate::leanh::lean_ctor_get(v___x_5935_, 1);
                v_ngen_5939_ = crate::leanh::lean_ctor_get(v___x_5935_, 2);
                v_auxDeclNGen_5940_ = crate::leanh::lean_ctor_get(v___x_5935_, 3);
                v_cache_5941_ = crate::leanh::lean_ctor_get(v___x_5935_, 5);
                v_messages_5942_ = crate::leanh::lean_ctor_get(v___x_5935_, 6);
                v_infoState_5943_ = crate::leanh::lean_ctor_get(v___x_5935_, 7);
                v_snapshotTasks_5944_ = crate::leanh::lean_ctor_get(v___x_5935_, 8);
                v_isSharedCheck_5974_ = (!crate::leanh::lean_is_exclusive(v___x_5935_)) as u8;
                if v_isSharedCheck_5974_ == 0 {
                    v___x_5946_ = v___x_5935_;
                    v_isShared_5947_ = v_isSharedCheck_5974_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5944_);
                    crate::leanh::lean_inc(v_infoState_5943_);
                    crate::leanh::lean_inc(v_messages_5942_);
                    crate::leanh::lean_inc(v_cache_5941_);
                    crate::leanh::lean_inc(v_traceState_5936_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5940_);
                    crate::leanh::lean_inc(v_ngen_5939_);
                    crate::leanh::lean_inc(v_nextMacroScope_5938_);
                    crate::leanh::lean_inc(v_env_5937_);
                    crate::leanh::lean_dec(v___x_5935_);
                    v___x_5946_ = crate::leanh::lean_box(0);
                    v_isShared_5947_ = v_isSharedCheck_5974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5948_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_5936_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_5949_ = crate::leanh::lean_ctor_get(v_traceState_5936_, 0);
                v_isSharedCheck_5973_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_5936_)) as u8;
                if v_isSharedCheck_5973_ == 0 {
                    v___x_5951_ = v_traceState_5936_;
                    v_isShared_5952_ = v_isSharedCheck_5973_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_5949_);
                    crate::leanh::lean_dec(v_traceState_5936_);
                    v___x_5951_ = crate::leanh::lean_box(0);
                    v_isShared_5952_ = v_isSharedCheck_5973_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5953_ = crate::leanh::lean_box(0);
                v___x_5954_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0);
                v___x_5955_ = 0;
                v___x_5956_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14;
                v___x_5957_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_5957_, 0, v_cls_5922_);
                crate::leanh::lean_ctor_set(v___x_5957_, 1, v___x_5953_);
                crate::leanh::lean_ctor_set(v___x_5957_, 2, v___x_5956_);
                crate::leanh::lean_ctor_set_float(
                    v___x_5957_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5954_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_5957_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_5954_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5957_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_5955_,
                );
                v___x_5958_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__1;
                v___x_5959_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5959_, 0, v___x_5957_);
                crate::leanh::lean_ctor_set(v___x_5959_, 1, v_a_5931_);
                crate::leanh::lean_ctor_set(v___x_5959_, 2, v___x_5958_);
                crate::leanh::lean_inc(v_ref_5929_);
                v___x_5960_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5960_, 0, v_ref_5929_);
                crate::leanh::lean_ctor_set(v___x_5960_, 1, v___x_5959_);
                v___x_5961_ = l_Lean_PersistentArray_push___redArg(v_traces_5949_, v___x_5960_);
                if v_isShared_5952_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5951_, 0, v___x_5961_);
                    v___x_5963_ = v___x_5951_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5972_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5972_, 0, v___x_5961_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5972_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_5948_,
                    );
                    v___x_5963_ = v_reuseFailAlloc_5972_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5947_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5946_, 4, v___x_5963_);
                    v___x_5965_ = v___x_5946_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5971_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5971_, 0, v_env_5937_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5971_, 1, v_nextMacroScope_5938_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5971_, 2, v_ngen_5939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5971_, 3, v_auxDeclNGen_5940_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5971_, 4, v___x_5963_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5971_, 5, v_cache_5941_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5971_, 6, v_messages_5942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5971_, 7, v_infoState_5943_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5971_, 8, v_snapshotTasks_5944_);
                    v___x_5965_ = v_reuseFailAlloc_5971_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5966_ = lean_st_ref_set(v___y_5927_, v___x_5965_);
                v___x_5967_ = crate::leanh::lean_box(0);
                if v_isShared_5934_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5933_, 0, v___x_5967_);
                    v___x_5969_ = v___x_5933_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5970_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5970_, 0, v___x_5967_);
                    v___x_5969_ = v_reuseFailAlloc_5970_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5969_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___boxed(
    mut v_cls_5976_: *mut crate::leanh::LeanObject,
    mut v_msg_5977_: *mut crate::leanh::LeanObject,
    mut v___y_5978_: *mut crate::leanh::LeanObject,
    mut v___y_5979_: *mut crate::leanh::LeanObject,
    mut v___y_5980_: *mut crate::leanh::LeanObject,
    mut v___y_5981_: *mut crate::leanh::LeanObject,
    mut v___y_5982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5983_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(v_cls_5976_, v_msg_5977_, v___y_5978_, v___y_5979_, v___y_5980_, v___y_5981_);
    crate::leanh::lean_dec(v___y_5981_);
    crate::leanh::lean_dec_ref(v___y_5980_);
    crate::leanh::lean_dec(v___y_5979_);
    crate::leanh::lean_dec_ref(v___y_5978_);
    return v_res_5983_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5991_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0;
    v___x_5992_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__2;
    v___x_5993_ = l_Lean_Name_append(v___x_5992_, v___x_5991_);
    return v___x_5993_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5995_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__4;
    v___x_5996_ = l_Lean_stringToMessageData(v___x_5995_);
    return v___x_5996_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd(
    mut v_declName_5997_: *mut crate::leanh::LeanObject,
    mut v_a_5998_: *mut crate::leanh::LeanObject,
    mut v_a_5999_: *mut crate::leanh::LeanObject,
    mut v_a_6000_: *mut crate::leanh::LeanObject,
    mut v_a_6001_: *mut crate::leanh::LeanObject,
    mut v_a_6002_: *mut crate::leanh::LeanObject,
    mut v_a_6003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: u8 = 0;
    let mut v___x_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6020_: u8 = 0;
    let mut v_inheritedTraceOptions_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6022_: u8 = 0;
    let mut v___x_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: u8 = 0;
    let mut v___x_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6043_: u8 = 0;
    let mut v___x_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6047_: u8 = 0;
    let mut v_unused_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6052_: u8 = 0;
    let mut v___x_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6056_: u8 = 0;
    let mut v_isSharedCheck_6057_: u8 = 0;
    let mut v_a_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6061_: u8 = 0;
    let mut v___x_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6065_: u8 = 0;
    let mut v_a_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6069_: u8 = 0;
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6073_: u8 = 0;
    let mut v_a_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6077_: u8 = 0;
    let mut v___x_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6081_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6005_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1;
                v___x_6006_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53;
                v___x_6007_ = 1;
                crate::leanh::lean_inc(v_declName_5997_);
                v___x_6008_ = l_Lean_Elab_Deriving_mkContext(
                    v___x_6005_,
                    v___x_6006_,
                    v_declName_5997_,
                    v___x_6007_,
                    v_a_5998_,
                    v_a_5999_,
                    v_a_6000_,
                    v_a_6001_,
                    v_a_6002_,
                    v_a_6003_,
                );
                if crate::leanh::lean_obj_tag(v___x_6008_) == 0 {
                    v_a_6009_ = crate::leanh::lean_ctor_get(v___x_6008_, 0);
                    crate::leanh::lean_inc(v_a_6009_);
                    crate::leanh::lean_dec_ref_known(v___x_6008_, 1);
                    v___x_6010_ = l_Lean_Elab_Deriving_Repr_mkMutualBlock(
                        v_a_6009_, v_a_5998_, v_a_5999_, v_a_6000_, v_a_6001_, v_a_6002_, v_a_6003_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6010_) == 0 {
                        v_a_6011_ = crate::leanh::lean_ctor_get(v___x_6010_, 0);
                        crate::leanh::lean_inc(v_a_6011_);
                        crate::leanh::lean_dec_ref_known(v___x_6010_, 1);
                        v___x_6012_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6013_ = lean_mk_empty_array_with_capacity(v___x_6012_);
                        crate::leanh::lean_inc_ref(v___x_6013_);
                        v___x_6014_ = lean_array_push(v___x_6013_, v_declName_5997_);
                        v___x_6015_ = l_Lean_Elab_Deriving_mkInstanceCmds(
                            v_a_6009_,
                            v___x_6005_,
                            v___x_6014_,
                            v___x_6007_,
                            v_a_5998_,
                            v_a_5999_,
                            v_a_6000_,
                            v_a_6001_,
                            v_a_6002_,
                            v_a_6003_,
                        );
                        crate::leanh::lean_dec_ref(v___x_6014_);
                        if crate::leanh::lean_obj_tag(v___x_6015_) == 0 {
                            v_options_6016_ = crate::leanh::lean_ctor_get(v_a_6002_, 2);
                            v_a_6017_ = crate::leanh::lean_ctor_get(v___x_6015_, 0);
                            v_isSharedCheck_6057_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6015_)) as u8;
                            if v_isSharedCheck_6057_ == 0 {
                                v___x_6019_ = v___x_6015_;
                                v_isShared_6020_ = v_isSharedCheck_6057_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6017_);
                                crate::leanh::lean_dec(v___x_6015_);
                                v___x_6019_ = crate::leanh::lean_box(0);
                                v_isShared_6020_ = v_isSharedCheck_6057_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_6013_);
                            crate::leanh::lean_dec(v_a_6011_);
                            v_a_6058_ = crate::leanh::lean_ctor_get(v___x_6015_, 0);
                            v_isSharedCheck_6065_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6015_)) as u8;
                            if v_isSharedCheck_6065_ == 0 {
                                v___x_6060_ = v___x_6015_;
                                v_isShared_6061_ = v_isSharedCheck_6065_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6058_);
                                crate::leanh::lean_dec(v___x_6015_);
                                v___x_6060_ = crate::leanh::lean_box(0);
                                v_isShared_6061_ = v_isSharedCheck_6065_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6009_);
                        crate::leanh::lean_dec(v_declName_5997_);
                        v_a_6066_ = crate::leanh::lean_ctor_get(v___x_6010_, 0);
                        v_isSharedCheck_6073_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6010_)) as u8;
                        if v_isSharedCheck_6073_ == 0 {
                            v___x_6068_ = v___x_6010_;
                            v_isShared_6069_ = v_isSharedCheck_6073_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6066_);
                            crate::leanh::lean_dec(v___x_6010_);
                            v___x_6068_ = crate::leanh::lean_box(0);
                            v_isShared_6069_ = v_isSharedCheck_6073_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_5997_);
                    v_a_6074_ = crate::leanh::lean_ctor_get(v___x_6008_, 0);
                    v_isSharedCheck_6081_ = (!crate::leanh::lean_is_exclusive(v___x_6008_)) as u8;
                    if v_isSharedCheck_6081_ == 0 {
                        v___x_6076_ = v___x_6008_;
                        v_isShared_6077_ = v_isSharedCheck_6081_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6074_);
                        crate::leanh::lean_dec(v___x_6008_);
                        v___x_6076_ = crate::leanh::lean_box(0);
                        v_isShared_6077_ = v_isSharedCheck_6081_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v_inheritedTraceOptions_6021_ = crate::leanh::lean_ctor_get(v_a_6002_, 13);
                v_hasTrace_6022_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_6016_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_6023_ = lean_array_push(v___x_6013_, v_a_6011_);
                v___x_6024_ = l_Array_append___redArg(v___x_6023_, v_a_6017_);
                crate::leanh::lean_dec(v_a_6017_);
                if v_hasTrace_6022_ == 0 {
                    if v_isShared_6020_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6019_, 0, v___x_6024_);
                        v___x_6026_ = v___x_6019_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6027_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6027_, 0, v___x_6024_);
                        v___x_6026_ = v_reuseFailAlloc_6027_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6028_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0;
                    v___x_6029_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3_once), _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3);
                    v___x_6030_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_6021_,
                        v_options_6016_,
                        v___x_6029_,
                    );
                    if v___x_6030_ == 0 {
                        if v_isShared_6020_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6019_, 0, v___x_6024_);
                            v___x_6032_ = v___x_6019_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6033_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6033_, 0, v___x_6024_);
                            v___x_6032_ = v_reuseFailAlloc_6033_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6019_);
                        v___x_6034_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5_once), _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5);
                        crate::leanh::lean_inc_ref(v___x_6024_);
                        v___x_6035_ = lean_array_to_list(v___x_6024_);
                        v___x_6036_ = crate::leanh::lean_box(0);
                        v___x_6037_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__0(v___x_6035_, v___x_6036_);
                        v___x_6038_ = l_Lean_MessageData_ofList(v___x_6037_);
                        v___x_6039_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6039_, 0, v___x_6034_);
                        crate::leanh::lean_ctor_set(v___x_6039_, 1, v___x_6038_);
                        v___x_6040_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(v___x_6028_, v___x_6039_, v_a_6000_, v_a_6001_, v_a_6002_, v_a_6003_);
                        if crate::leanh::lean_obj_tag(v___x_6040_) == 0 {
                            v_isSharedCheck_6047_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6040_)) as u8;
                            if v_isSharedCheck_6047_ == 0 {
                                v_unused_6048_ = crate::leanh::lean_ctor_get(v___x_6040_, 0);
                                crate::leanh::lean_dec(v_unused_6048_);
                                v___x_6042_ = v___x_6040_;
                                v_isShared_6043_ = v_isSharedCheck_6047_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_6040_);
                                v___x_6042_ = crate::leanh::lean_box(0);
                                v_isShared_6043_ = v_isSharedCheck_6047_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_6024_);
                            v_a_6049_ = crate::leanh::lean_ctor_get(v___x_6040_, 0);
                            v_isSharedCheck_6056_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6040_)) as u8;
                            if v_isSharedCheck_6056_ == 0 {
                                v___x_6051_ = v___x_6040_;
                                v_isShared_6052_ = v_isSharedCheck_6056_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6049_);
                                crate::leanh::lean_dec(v___x_6040_);
                                v___x_6051_ = crate::leanh::lean_box(0);
                                v_isShared_6052_ = v_isSharedCheck_6056_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_6026_;
            }
            3 => {
                return v___x_6032_;
            }
            4 => {
                if v_isShared_6043_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6042_, 0, v___x_6024_);
                    v___x_6045_ = v___x_6042_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6046_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6046_, 0, v___x_6024_);
                    v___x_6045_ = v_reuseFailAlloc_6046_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6045_;
            }
            6 => {
                if v_isShared_6052_ == 0 {
                    v___x_6054_ = v___x_6051_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6055_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6055_, 0, v_a_6049_);
                    v___x_6054_ = v_reuseFailAlloc_6055_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6054_;
            }
            8 => {
                if v_isShared_6061_ == 0 {
                    v___x_6063_ = v___x_6060_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6064_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6064_, 0, v_a_6058_);
                    v___x_6063_ = v_reuseFailAlloc_6064_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6063_;
            }
            10 => {
                if v_isShared_6069_ == 0 {
                    v___x_6071_ = v___x_6068_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6072_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_a_6066_);
                    v___x_6071_ = v_reuseFailAlloc_6072_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6071_;
            }
            12 => {
                if v_isShared_6077_ == 0 {
                    v___x_6079_ = v___x_6076_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6080_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6080_, 0, v_a_6074_);
                    v___x_6079_ = v_reuseFailAlloc_6080_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6079_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___boxed(
    mut v_declName_6082_: *mut crate::leanh::LeanObject,
    mut v_a_6083_: *mut crate::leanh::LeanObject,
    mut v_a_6084_: *mut crate::leanh::LeanObject,
    mut v_a_6085_: *mut crate::leanh::LeanObject,
    mut v_a_6086_: *mut crate::leanh::LeanObject,
    mut v_a_6087_: *mut crate::leanh::LeanObject,
    mut v_a_6088_: *mut crate::leanh::LeanObject,
    mut v_a_6089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6090_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd(
        v_declName_6082_,
        v_a_6083_,
        v_a_6084_,
        v_a_6085_,
        v_a_6086_,
        v_a_6087_,
        v_a_6088_,
    );
    crate::leanh::lean_dec(v_a_6088_);
    crate::leanh::lean_dec_ref(v_a_6087_);
    crate::leanh::lean_dec(v_a_6086_);
    crate::leanh::lean_dec_ref(v_a_6085_);
    crate::leanh::lean_dec(v_a_6084_);
    crate::leanh::lean_dec_ref(v_a_6083_);
    return v_res_6090_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1(
    mut v_cls_6091_: *mut crate::leanh::LeanObject,
    mut v_msg_6092_: *mut crate::leanh::LeanObject,
    mut v___y_6093_: *mut crate::leanh::LeanObject,
    mut v___y_6094_: *mut crate::leanh::LeanObject,
    mut v___y_6095_: *mut crate::leanh::LeanObject,
    mut v___y_6096_: *mut crate::leanh::LeanObject,
    mut v___y_6097_: *mut crate::leanh::LeanObject,
    mut v___y_6098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6100_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(v_cls_6091_, v_msg_6092_, v___y_6095_, v___y_6096_, v___y_6097_, v___y_6098_);
    return v___x_6100_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___boxed(
    mut v_cls_6101_: *mut crate::leanh::LeanObject,
    mut v_msg_6102_: *mut crate::leanh::LeanObject,
    mut v___y_6103_: *mut crate::leanh::LeanObject,
    mut v___y_6104_: *mut crate::leanh::LeanObject,
    mut v___y_6105_: *mut crate::leanh::LeanObject,
    mut v___y_6106_: *mut crate::leanh::LeanObject,
    mut v___y_6107_: *mut crate::leanh::LeanObject,
    mut v___y_6108_: *mut crate::leanh::LeanObject,
    mut v___y_6109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6110_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1(v_cls_6101_, v_msg_6102_, v___y_6103_, v___y_6104_, v___y_6105_, v___y_6106_, v___y_6107_, v___y_6108_);
    crate::leanh::lean_dec(v___y_6108_);
    crate::leanh::lean_dec_ref(v___y_6107_);
    crate::leanh::lean_dec(v___y_6106_);
    crate::leanh::lean_dec_ref(v___y_6105_);
    crate::leanh::lean_dec(v___y_6104_);
    crate::leanh::lean_dec_ref(v___y_6103_);
    return v_res_6110_;
}
pub unsafe fn l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(
    mut v_declName_6111_: *mut crate::leanh::LeanObject,
    mut v___y_6112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: u8 = 0;
    let mut v___x_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6114_ = lean_st_ref_get(v___y_6112_);
    v_env_6115_ = crate::leanh::lean_ctor_get(v___x_6114_, 0);
    crate::leanh::lean_inc_ref(v_env_6115_);
    crate::leanh::lean_dec(v___x_6114_);
    v___x_6116_ = l_Lean_isInductiveCore(v_env_6115_, v_declName_6111_);
    v___x_6117_ = crate::leanh::lean_box((v___x_6116_) as usize);
    v___x_6118_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6118_, 0, v___x_6117_);
    return v___x_6118_;
}
pub unsafe fn l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg___boxed(
    mut v_declName_6119_: *mut crate::leanh::LeanObject,
    mut v___y_6120_: *mut crate::leanh::LeanObject,
    mut v___y_6121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6122_ =
        l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(
            v_declName_6119_,
            v___y_6120_,
        );
    crate::leanh::lean_dec(v___y_6120_);
    return v_res_6122_;
}
pub unsafe fn l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0(
    mut v_declName_6123_: *mut crate::leanh::LeanObject,
    mut v___y_6124_: *mut crate::leanh::LeanObject,
    mut v___y_6125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6127_ =
        l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(
            v_declName_6123_,
            v___y_6125_,
        );
    return v___x_6127_;
}
pub unsafe fn l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___boxed(
    mut v_declName_6128_: *mut crate::leanh::LeanObject,
    mut v___y_6129_: *mut crate::leanh::LeanObject,
    mut v___y_6130_: *mut crate::leanh::LeanObject,
    mut v___y_6131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6132_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0(
        v_declName_6128_,
        v___y_6129_,
        v___y_6130_,
    );
    crate::leanh::lean_dec(v___y_6130_);
    crate::leanh::lean_dec_ref(v___y_6129_);
    return v_res_6132_;
}
pub unsafe fn l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(
    mut v_____do__lift_6133_: u8,
    mut v___y_6134_: *mut crate::leanh::LeanObject,
    mut v___y_6135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_6133_ == 0 {
        let mut v___x_6137_: u8 = 0;
        let mut v___x_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6137_ = 1;
        v___x_6138_ = crate::leanh::lean_box((v___x_6137_) as usize);
        v___x_6139_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6139_, 0, v___x_6138_);
        return v___x_6139_;
    } else {
        let mut v___x_6140_: u8 = 0;
        let mut v___x_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6140_ = 0;
        v___x_6141_ = crate::leanh::lean_box((v___x_6140_) as usize);
        v___x_6142_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6142_, 0, v___x_6141_);
        return v___x_6142_;
    }
}
pub unsafe fn l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0___boxed(
    mut v_____do__lift_6143_: *mut crate::leanh::LeanObject,
    mut v___y_6144_: *mut crate::leanh::LeanObject,
    mut v___y_6145_: *mut crate::leanh::LeanObject,
    mut v___y_6146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_2462__boxed_6147_: u8 = 0;
    let mut v_res_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_2462__boxed_6147_ = (crate::leanh::lean_unbox(v_____do__lift_6143_) as u8);
    v_res_6148_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(
        v_____do__lift_2462__boxed_6147_,
        v___y_6144_,
        v___y_6145_,
    );
    crate::leanh::lean_dec(v___y_6145_);
    crate::leanh::lean_dec_ref(v___y_6144_);
    return v_res_6148_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(
    mut v_as_6149_: *mut crate::leanh::LeanObject,
    mut v_i_6150_: usize,
    mut v_stop_6151_: usize,
    mut v_b_6152_: *mut crate::leanh::LeanObject,
    mut v___y_6153_: *mut crate::leanh::LeanObject,
    mut v___y_6154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6156_: u8 = 0;
    let mut v___x_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: usize = 0;
    let mut v___x_6161_: usize = 0;
    let mut v___x_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6156_ = lean_usize_dec_eq(v_i_6150_, v_stop_6151_);
                if v___x_6156_ == 0 {
                    v___x_6157_ = lean_array_uget_borrowed(v_as_6149_, v_i_6150_);
                    crate::leanh::lean_inc(v___x_6157_);
                    v___x_6158_ =
                        l_Lean_Elab_Command_elabCommand(v___x_6157_, v___y_6153_, v___y_6154_);
                    if crate::leanh::lean_obj_tag(v___x_6158_) == 0 {
                        v_a_6159_ = crate::leanh::lean_ctor_get(v___x_6158_, 0);
                        crate::leanh::lean_inc(v_a_6159_);
                        crate::leanh::lean_dec_ref_known(v___x_6158_, 1);
                        v___x_6160_ = 1usize;
                        v___x_6161_ = lean_usize_add(v_i_6150_, v___x_6160_);
                        v_i_6150_ = v___x_6161_;
                        v_b_6152_ = v_a_6159_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6158_;
                    }
                } else {
                    v___x_6163_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6163_, 0, v_b_6152_);
                    return v___x_6163_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1___boxed(
    mut v_as_6164_: *mut crate::leanh::LeanObject,
    mut v_i_6165_: *mut crate::leanh::LeanObject,
    mut v_stop_6166_: *mut crate::leanh::LeanObject,
    mut v_b_6167_: *mut crate::leanh::LeanObject,
    mut v___y_6168_: *mut crate::leanh::LeanObject,
    mut v___y_6169_: *mut crate::leanh::LeanObject,
    mut v___y_6170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6171_: usize = 0;
    let mut v_stop_boxed_6172_: usize = 0;
    let mut v_res_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6171_ = crate::leanh::lean_unbox_usize(v_i_6165_);
    crate::leanh::lean_dec(v_i_6165_);
    v_stop_boxed_6172_ = crate::leanh::lean_unbox_usize(v_stop_6166_);
    crate::leanh::lean_dec(v_stop_6166_);
    v_res_6173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(v_as_6164_, v_i_boxed_6171_, v_stop_boxed_6172_, v_b_6167_, v___y_6168_, v___y_6169_);
    crate::leanh::lean_dec(v___y_6169_);
    crate::leanh::lean_dec_ref(v___y_6168_);
    crate::leanh::lean_dec_ref(v_as_6164_);
    return v_res_6173_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0(
    mut v___x_6174_: *mut crate::leanh::LeanObject,
    mut v___x_6175_: *mut crate::leanh::LeanObject,
    mut v___x_6176_: *mut crate::leanh::LeanObject,
    mut v___y_6177_: *mut crate::leanh::LeanObject,
    mut v___y_6178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6184_: u8 = 0;
    let mut v___x_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: u8 = 0;
    let mut v___x_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: u8 = 0;
    let mut v___x_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: usize = 0;
    let mut v___x_6195_: usize = 0;
    let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: usize = 0;
    let mut v___x_6198_: usize = 0;
    let mut v___x_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6200_: u8 = 0;
    let mut v_a_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6204_: u8 = 0;
    let mut v___x_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6208_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6180_ = l_Lean_Elab_Command_liftTermElabM___redArg(
                    v___x_6174_,
                    v___y_6177_,
                    v___y_6178_,
                );
                if crate::leanh::lean_obj_tag(v___x_6180_) == 0 {
                    v_a_6181_ = crate::leanh::lean_ctor_get(v___x_6180_, 0);
                    v_isSharedCheck_6200_ = (!crate::leanh::lean_is_exclusive(v___x_6180_)) as u8;
                    if v_isSharedCheck_6200_ == 0 {
                        v___x_6183_ = v___x_6180_;
                        v_isShared_6184_ = v_isSharedCheck_6200_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6181_);
                        crate::leanh::lean_dec(v___x_6180_);
                        v___x_6183_ = crate::leanh::lean_box(0);
                        v_isShared_6184_ = v_isSharedCheck_6200_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6201_ = crate::leanh::lean_ctor_get(v___x_6180_, 0);
                    v_isSharedCheck_6208_ = (!crate::leanh::lean_is_exclusive(v___x_6180_)) as u8;
                    if v_isSharedCheck_6208_ == 0 {
                        v___x_6203_ = v___x_6180_;
                        v_isShared_6204_ = v_isSharedCheck_6208_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6201_);
                        crate::leanh::lean_dec(v___x_6180_);
                        v___x_6203_ = crate::leanh::lean_box(0);
                        v_isShared_6204_ = v_isSharedCheck_6208_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6185_ = lean_array_get_size(v_a_6181_);
                v___x_6186_ = lean_nat_dec_lt(v___x_6175_, v___x_6185_);
                if v___x_6186_ == 0 {
                    crate::leanh::lean_dec(v_a_6181_);
                    if v_isShared_6184_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6183_, 0, v___x_6176_);
                        v___x_6188_ = v___x_6183_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6189_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6189_, 0, v___x_6176_);
                        v___x_6188_ = v_reuseFailAlloc_6189_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6190_ = lean_nat_dec_le(v___x_6185_, v___x_6185_);
                    if v___x_6190_ == 0 {
                        if v___x_6186_ == 0 {
                            crate::leanh::lean_dec(v_a_6181_);
                            if v_isShared_6184_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_6183_, 0, v___x_6176_);
                                v___x_6192_ = v___x_6183_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_6193_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6193_, 0, v___x_6176_);
                                v___x_6192_ = v_reuseFailAlloc_6193_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_6183_);
                            v___x_6194_ = 0usize;
                            v___x_6195_ = lean_usize_of_nat(v___x_6185_);
                            v___x_6196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(v_a_6181_, v___x_6194_, v___x_6195_, v___x_6176_, v___y_6177_, v___y_6178_);
                            crate::leanh::lean_dec(v_a_6181_);
                            return v___x_6196_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6183_);
                        v___x_6197_ = 0usize;
                        v___x_6198_ = lean_usize_of_nat(v___x_6185_);
                        v___x_6199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(v_a_6181_, v___x_6197_, v___x_6198_, v___x_6176_, v___y_6177_, v___y_6178_);
                        crate::leanh::lean_dec(v_a_6181_);
                        return v___x_6199_;
                    }
                }
            }
            2 => {
                return v___x_6188_;
            }
            3 => {
                return v___x_6192_;
            }
            4 => {
                if v_isShared_6204_ == 0 {
                    v___x_6206_ = v___x_6203_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6207_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6207_, 0, v_a_6201_);
                    v___x_6206_ = v_reuseFailAlloc_6207_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6206_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0___boxed(
    mut v___x_6209_: *mut crate::leanh::LeanObject,
    mut v___x_6210_: *mut crate::leanh::LeanObject,
    mut v___x_6211_: *mut crate::leanh::LeanObject,
    mut v___y_6212_: *mut crate::leanh::LeanObject,
    mut v___y_6213_: *mut crate::leanh::LeanObject,
    mut v___y_6214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0(v___x_6209_, v___x_6210_, v___x_6211_, v___y_6212_, v___y_6213_);
    crate::leanh::lean_dec(v___y_6213_);
    crate::leanh::lean_dec_ref(v___y_6212_);
    crate::leanh::lean_dec(v___x_6210_);
    return v_res_6215_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(
    mut v_as_6216_: *mut crate::leanh::LeanObject,
    mut v_sz_6217_: usize,
    mut v_i_6218_: usize,
    mut v_b_6219_: *mut crate::leanh::LeanObject,
    mut v___y_6220_: *mut crate::leanh::LeanObject,
    mut v___y_6221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6223_: u8 = 0;
    let mut v___x_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: usize = 0;
    let mut v___x_6232_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6223_ = lean_usize_dec_lt(v_i_6218_, v_sz_6217_);
                if v___x_6223_ == 0 {
                    v___x_6224_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6224_, 0, v_b_6219_);
                    return v___x_6224_;
                } else {
                    v___x_6225_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6226_ = crate::leanh::lean_box(0);
                    v_a_6227_ = lean_array_uget_borrowed(v_as_6216_, v_i_6218_);
                    crate::leanh::lean_inc_n(v_a_6227_, 2);
                    v___x_6228_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___boxed as *mut core::ffi::c_void, 8, 1);
                    crate::leanh::lean_closure_set(v___x_6228_, 0, v_a_6227_);
                    v___f_6229_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0___boxed as *mut core::ffi::c_void, 6, 3);
                    crate::leanh::lean_closure_set(v___f_6229_, 0, v___x_6228_);
                    crate::leanh::lean_closure_set(v___f_6229_, 1, v___x_6225_);
                    crate::leanh::lean_closure_set(v___f_6229_, 2, v___x_6226_);
                    v___x_6230_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(
                        v_a_6227_,
                        v___f_6229_,
                        v___y_6220_,
                        v___y_6221_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6230_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6230_, 1);
                        v___x_6231_ = 1usize;
                        v___x_6232_ = lean_usize_add(v_i_6218_, v___x_6231_);
                        v_i_6218_ = v___x_6232_;
                        v_b_6219_ = v___x_6226_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6230_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___boxed(
    mut v_as_6234_: *mut crate::leanh::LeanObject,
    mut v_sz_6235_: *mut crate::leanh::LeanObject,
    mut v_i_6236_: *mut crate::leanh::LeanObject,
    mut v_b_6237_: *mut crate::leanh::LeanObject,
    mut v___y_6238_: *mut crate::leanh::LeanObject,
    mut v___y_6239_: *mut crate::leanh::LeanObject,
    mut v___y_6240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6241_: usize = 0;
    let mut v_i_boxed_6242_: usize = 0;
    let mut v_res_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6241_ = crate::leanh::lean_unbox_usize(v_sz_6235_);
    crate::leanh::lean_dec(v_sz_6235_);
    v_i_boxed_6242_ = crate::leanh::lean_unbox_usize(v_i_6236_);
    crate::leanh::lean_dec(v_i_6236_);
    v_res_6243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(v_as_6234_, v_sz_boxed_6241_, v_i_boxed_6242_, v_b_6237_, v___y_6238_, v___y_6239_);
    crate::leanh::lean_dec(v___y_6239_);
    crate::leanh::lean_dec_ref(v___y_6238_);
    crate::leanh::lean_dec_ref(v_as_6234_);
    return v_res_6243_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3(
    mut v_as_6244_: *mut crate::leanh::LeanObject,
    mut v_i_6245_: usize,
    mut v_stop_6246_: usize,
    mut v___y_6247_: *mut crate::leanh::LeanObject,
    mut v___y_6248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6250_: u8 = 0;
    let mut v___x_6251_: u8 = 0;
    let mut v_a_6253_: u8 = 0;
    let mut v___x_6254_: usize = 0;
    let mut v___x_6255_: usize = 0;
    let mut v___x_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6264_: u8 = 0;
    let mut v___x_6265_: u8 = 0;
    let mut v___x_6266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6270_: u8 = 0;
    let mut v_a_6271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: u8 = 0;
    let mut v___x_6273_: u8 = 0;
    let mut v___x_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6250_ = lean_usize_dec_eq(v_i_6245_, v_stop_6246_);
                if v___x_6250_ == 0 {
                    v___x_6251_ = 1;
                    v___x_6259_ = lean_array_uget_borrowed(v_as_6244_, v_i_6245_);
                    crate::leanh::lean_inc(v___x_6259_);
                    v___x_6260_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(v___x_6259_, v___y_6248_);
                    if crate::leanh::lean_obj_tag(v___x_6260_) == 0 {
                        v_a_6261_ = crate::leanh::lean_ctor_get(v___x_6260_, 0);
                        v_isSharedCheck_6270_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6260_)) as u8;
                        if v_isSharedCheck_6270_ == 0 {
                            v___x_6263_ = v___x_6260_;
                            v_isShared_6264_ = v_isSharedCheck_6270_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6261_);
                            crate::leanh::lean_dec(v___x_6260_);
                            v___x_6263_ = crate::leanh::lean_box(0);
                            v_isShared_6264_ = v_isSharedCheck_6270_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_6260_) == 0 {
                            v_a_6271_ = crate::leanh::lean_ctor_get(v___x_6260_, 0);
                            crate::leanh::lean_inc(v_a_6271_);
                            crate::leanh::lean_dec_ref_known(v___x_6260_, 1);
                            v___x_6272_ = (crate::leanh::lean_unbox(v_a_6271_) as u8);
                            crate::leanh::lean_dec(v_a_6271_);
                            v_a_6253_ = v___x_6272_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_6260_;
                        }
                    }
                } else {
                    v___x_6273_ = 0;
                    v___x_6274_ = crate::leanh::lean_box((v___x_6273_) as usize);
                    v___x_6275_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6275_, 0, v___x_6274_);
                    return v___x_6275_;
                }
            }
            1 => {
                if v_a_6253_ == 0 {
                    v___x_6254_ = 1usize;
                    v___x_6255_ = lean_usize_add(v_i_6245_, v___x_6254_);
                    v_i_6245_ = v___x_6255_;
                    state = 0;
                    continue;
                } else {
                    v___x_6257_ = crate::leanh::lean_box((v___x_6251_) as usize);
                    v___x_6258_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6258_, 0, v___x_6257_);
                    return v___x_6258_;
                }
            }
            2 => {
                v___x_6265_ = (crate::leanh::lean_unbox(v_a_6261_) as u8);
                crate::leanh::lean_dec(v_a_6261_);
                if v___x_6265_ == 0 {
                    v___x_6266_ = crate::leanh::lean_box((v___x_6251_) as usize);
                    if v_isShared_6264_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6263_, 0, v___x_6266_);
                        v___x_6268_ = v___x_6263_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6269_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6269_, 0, v___x_6266_);
                        v___x_6268_ = v_reuseFailAlloc_6269_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6263_);
                    v_a_6253_ = v___x_6250_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_6268_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3___boxed(
    mut v_as_6276_: *mut crate::leanh::LeanObject,
    mut v_i_6277_: *mut crate::leanh::LeanObject,
    mut v_stop_6278_: *mut crate::leanh::LeanObject,
    mut v___y_6279_: *mut crate::leanh::LeanObject,
    mut v___y_6280_: *mut crate::leanh::LeanObject,
    mut v___y_6281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6282_: usize = 0;
    let mut v_stop_boxed_6283_: usize = 0;
    let mut v_res_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6282_ = crate::leanh::lean_unbox_usize(v_i_6277_);
    crate::leanh::lean_dec(v_i_6277_);
    v_stop_boxed_6283_ = crate::leanh::lean_unbox_usize(v_stop_6278_);
    crate::leanh::lean_dec(v_stop_6278_);
    v_res_6284_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3(v_as_6276_, v_i_boxed_6282_, v_stop_boxed_6283_, v___y_6279_, v___y_6280_);
    crate::leanh::lean_dec(v___y_6280_);
    crate::leanh::lean_dec_ref(v___y_6279_);
    crate::leanh::lean_dec_ref(v_as_6276_);
    return v_res_6284_;
}
pub unsafe fn l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler(
    mut v_declNames_6285_: *mut crate::leanh::LeanObject,
    mut v_a_6286_: *mut crate::leanh::LeanObject,
    mut v_a_6287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6291_: usize = 0;
    let mut v___x_6292_: usize = 0;
    let mut v___x_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6296_: u8 = 0;
    let mut v___x_6297_: u8 = 0;
    let mut v___x_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6302_: u8 = 0;
    let mut v_unused_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6307_: u8 = 0;
    let mut v___x_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6311_: u8 = 0;
    let mut v___y_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6315_: u8 = 0;
    let mut v___x_6316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: u8 = 0;
    let mut v___x_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: usize = 0;
    let mut v___x_6321_: usize = 0;
    let mut v___x_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: u8 = 0;
    let mut v___x_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6316_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6317_ = lean_array_get_size(v_declNames_6285_);
                v___x_6318_ = lean_nat_dec_lt(v___x_6316_, v___x_6317_);
                if v___x_6318_ == 0 {
                    v___x_6319_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(
                        v___x_6318_,
                        v_a_6286_,
                        v_a_6287_,
                    );
                    v___y_6313_ = v___x_6319_;
                    state = 6;
                    continue;
                } else {
                    if v___x_6318_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_6320_ = 0usize;
                        v___x_6321_ = lean_usize_of_nat(v___x_6317_);
                        v___x_6322_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3(v_declNames_6285_, v___x_6320_, v___x_6321_, v_a_6286_, v_a_6287_);
                        if crate::leanh::lean_obj_tag(v___x_6322_) == 0 {
                            v_a_6323_ = crate::leanh::lean_ctor_get(v___x_6322_, 0);
                            crate::leanh::lean_inc(v_a_6323_);
                            crate::leanh::lean_dec_ref_known(v___x_6322_, 1);
                            v___x_6324_ = (crate::leanh::lean_unbox(v_a_6323_) as u8);
                            crate::leanh::lean_dec(v_a_6323_);
                            v___x_6325_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(
                                v___x_6324_,
                                v_a_6286_,
                                v_a_6287_,
                            );
                            v___y_6313_ = v___x_6325_;
                            state = 6;
                            continue;
                        } else {
                            v___y_6313_ = v___x_6322_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6290_ = crate::leanh::lean_box(0);
                v_sz_6291_ = lean_array_size(v_declNames_6285_);
                v___x_6292_ = 0usize;
                v___x_6293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(v_declNames_6285_, v_sz_6291_, v___x_6292_, v___x_6290_, v_a_6286_, v_a_6287_);
                if crate::leanh::lean_obj_tag(v___x_6293_) == 0 {
                    v_isSharedCheck_6302_ = (!crate::leanh::lean_is_exclusive(v___x_6293_)) as u8;
                    if v_isSharedCheck_6302_ == 0 {
                        v_unused_6303_ = crate::leanh::lean_ctor_get(v___x_6293_, 0);
                        crate::leanh::lean_dec(v_unused_6303_);
                        v___x_6295_ = v___x_6293_;
                        v_isShared_6296_ = v_isSharedCheck_6302_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6293_);
                        v___x_6295_ = crate::leanh::lean_box(0);
                        v_isShared_6296_ = v_isSharedCheck_6302_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_6304_ = crate::leanh::lean_ctor_get(v___x_6293_, 0);
                    v_isSharedCheck_6311_ = (!crate::leanh::lean_is_exclusive(v___x_6293_)) as u8;
                    if v_isSharedCheck_6311_ == 0 {
                        v___x_6306_ = v___x_6293_;
                        v_isShared_6307_ = v_isSharedCheck_6311_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6304_);
                        crate::leanh::lean_dec(v___x_6293_);
                        v___x_6306_ = crate::leanh::lean_box(0);
                        v_isShared_6307_ = v_isSharedCheck_6311_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6297_ = 1;
                v___x_6298_ = crate::leanh::lean_box((v___x_6297_) as usize);
                if v_isShared_6296_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6295_, 0, v___x_6298_);
                    v___x_6300_ = v___x_6295_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6301_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6301_, 0, v___x_6298_);
                    v___x_6300_ = v_reuseFailAlloc_6301_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6300_;
            }
            4 => {
                if v_isShared_6307_ == 0 {
                    v___x_6309_ = v___x_6306_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6310_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6310_, 0, v_a_6304_);
                    v___x_6309_ = v_reuseFailAlloc_6310_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6309_;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v___y_6313_) == 0 {
                    v_a_6314_ = crate::leanh::lean_ctor_get(v___y_6313_, 0);
                    v___x_6315_ = (crate::leanh::lean_unbox(v_a_6314_) as u8);
                    if v___x_6315_ == 0 {
                        return v___y_6313_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_6313_, 1);
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_6313_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___boxed(
    mut v_declNames_6326_: *mut crate::leanh::LeanObject,
    mut v_a_6327_: *mut crate::leanh::LeanObject,
    mut v_a_6328_: *mut crate::leanh::LeanObject,
    mut v_a_6329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6330_ =
        l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler(v_declNames_6326_, v_a_6327_, v_a_6328_);
    crate::leanh::lean_dec(v_a_6328_);
    crate::leanh::lean_dec_ref(v_a_6327_);
    crate::leanh::lean_dec_ref(v_declNames_6326_);
    return v_res_6330_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6398_ = l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1;
    v___x_6399_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__0_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_;
    v___x_6400_ = l_Lean_Elab_registerDerivingHandler(v___x_6398_, v___x_6399_);
    if crate::leanh::lean_obj_tag(v___x_6400_) == 0 {
        let mut v___x_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6402_: u8 = 0;
        let mut v___x_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_6400_, 1);
        v___x_6401_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0;
        v___x_6402_ = 0;
        v___x_6403_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__25_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_;
        v___x_6404_ = l_Lean_registerTraceClass(v___x_6401_, v___x_6402_, v___x_6403_);
        return v___x_6404_;
    } else {
        return v___x_6400_;
    }
}
pub unsafe fn l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2____boxed(
    mut v_a_6405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6406_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_();
    return v_res_6406_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Deriving_Repr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Inductive(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Deriving_Repr(
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
pub unsafe fn initialize_Lean_Elab_Deriving_Repr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Inductive(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_Repr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Deriving_Repr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Deriving_Repr(builtin);
}

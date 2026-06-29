// Lean compiler output
// Module: Lean.Elab.Deriving.Hashable
// Imports: Lean.Meta.Inductive Lean.Elab.Deriving.Basic Lean.Elab.Deriving.Util
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_mkNumLit, l_Lean_mkSepArray, lean_mk_syntax_ident,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_append, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_Syntax_node7,
    l_Lean_addMacroScope, l_Lean_mkAtom, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
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
    l_Lean_Environment_setExporting,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_getAppFn, l_Lean_instInhabitedExpr};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList,
    l_Lean_MessageData_ofSyntax, l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
};
use crate::r#gen::Lean::Meta::Inductive::{
    initialize_Lean_Meta_Inductive, runtime_initialize_Lean_Meta_Inductive,
};
use crate::r#gen::Lean::MonadEnv::l_Lean_isInductiveCore;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_mk, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_panic_fn_borrowed,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_whnf};
pub static l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0_value:
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
    m_data: [72, 97, 115, 104, 97, 98, 108, 101, 0],
};
static mut l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14048837327677012053 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__2_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__4_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__5_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [76, 101, 97, 110, 46, 105, 115, 67, 116, 111, 114, 63, 0]};
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__6_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__3_value) as *mut crate::leanh::LeanObject,3984140175429830279 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__5_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7839396180116328695 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__2_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__4_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [109, 105, 120, 72, 97, 115, 104, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__4_value) as *mut crate::leanh::LeanObject,1805407151482751677 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__6_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__7_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__9_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__9_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__11_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__11_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__11_value) as *mut crate::leanh::LeanObject,7932075773091973500 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__13_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__13_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__13_value) as *mut crate::leanh::LeanObject,7306243862518720553 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__15_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__16_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__16_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__18_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__20_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__21_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [68, 101, 114, 105, 118, 105, 110, 103, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__21_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__20_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__21_value) as *mut crate::leanh::LeanObject,15755466758005450470 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0_value) as *mut crate::leanh::LeanObject,18240382239870719436 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__23_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__22_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__24_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__24_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__25_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__25_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__25_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__24_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__26_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__25_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__26_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__27_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__27_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__27_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__27_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__27_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__28_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__27_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__30_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__30_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__30_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__20_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__30_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__30_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value) as *mut crate::leanh::LeanObject,16981400742628996529 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__31_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__30_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__32_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__31_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__33_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__28_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__32_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__33_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__34_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__26_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__33_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__34_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__35_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__23_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__34_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__35_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__36_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 97, 115, 104, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__36_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__38_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__36_value) as *mut crate::leanh::LeanObject,7690978804004710335 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__38_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__39_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0_value) as *mut crate::leanh::LeanObject,14048837327677012053 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__39_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__39_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__36_value) as *mut crate::leanh::LeanObject,11408791812338570225 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__39_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__40_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__39_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__40: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__40_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__41_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__40_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__41_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__42_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__42_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [64, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__1_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__1_value) as *mut crate::leanh::LeanObject,13290931718435096973 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__4_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 116, 99, 104, 65, 108, 116, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__4_value) as *mut crate::leanh::LeanObject;
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__4_value) as *mut crate::leanh::LeanObject,16529391333736644786 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__6_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__7_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__9_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__1_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkMatch___closed__0_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Deriving_Hashable_mkMatch___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11514550152210403337 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkMatch___closed__2_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Deriving_Hashable_mkMatch___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkMatch___closed__3_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Deriving_Hashable_mkMatch___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__3_value)
            as *mut crate::leanh::LeanObject,
        13242179749370575553 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__0_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8497769072906204829 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__2_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__2_value)
            as *mut crate::leanh::LeanObject,
        14557702332550915328 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__4_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__4_value)
            as *mut crate::leanh::LeanObject,
        2533412339571800130 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__6_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__7_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__7_value)
            as *mut crate::leanh::LeanObject,
        7499624980761693169 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__9_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__9_value)
            as *mut crate::leanh::LeanObject,
        7983999284776576032 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__11_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__12_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__12_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__11_value)
            as *mut crate::leanh::LeanObject,
        4584992172905639687 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__12_value)
            as *mut crate::leanh::LeanObject,
        3878072352281346923 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__14_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__16_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__14_value)
            as *mut crate::leanh::LeanObject,
        282208228266294739 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__17_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__18_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__18_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__18_value)
            as *mut crate::leanh::LeanObject,
        9789339221525904376 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__20_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__21_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__21_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__21_value)
            as *mut crate::leanh::LeanObject,
        1827444229220621555 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__23_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__23_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__23_value)
            as *mut crate::leanh::LeanObject,
        5473625859156281626 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__25_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__25_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__25_value)
            as *mut crate::leanh::LeanObject,
        4498178684837002829 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__27_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__28_value:
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
    m_data: [85, 73, 110, 116, 54, 52, 0],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__28_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__28_value)
            as *mut crate::leanh::LeanObject,
        2954612489107370298 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__31_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__32_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__33_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__32_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__34_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__31_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__33_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__34_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__35_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__35_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__35_value)
            as *mut crate::leanh::LeanObject,
        13585030837571646948 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__38_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__38_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__39_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__39_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__38_value)
            as *mut crate::leanh::LeanObject,
        7625897890118033792 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__39_value)
            as *mut crate::leanh::LeanObject,
        8715860392475343861 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41_value)
            as *mut crate::leanh::LeanObject,
        14919950218492817255 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__43_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__43_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__44_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__32_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__44_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__45_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__43_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__44_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__45: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__45_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__0_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__29_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__0_value)
            as *mut crate::leanh::LeanObject,
        76928035496447287 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__2_value:
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
static mut l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [104, 97, 115, 104, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__20_value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__21_value) as *mut crate::leanh::LeanObject,3113176348997436611 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__0_value) as *mut crate::leanh::LeanObject,16754874744598668869 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__2_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__5_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_Hashable_mkHashableHandler___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Deriving_Hashable_mkHashableHandler___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkHashableHandler___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__0_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Deriving_Hashable_mkHashableHandler___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__0_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__0_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__1_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__1_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__1_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__2_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__1_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__2_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__2_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__3_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__2_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__3_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__3_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__4_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__3_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__20_value) as *mut crate::leanh::LeanObject,5444244426488757208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__4_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__4_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__5_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__4_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__21_value) as *mut crate::leanh::LeanObject,5241190260012038858 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__5_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__5_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__6_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__5_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0_value) as *mut crate::leanh::LeanObject,12489139974650585456 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__6_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__6_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__7_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__6_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,15076099729257306697 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__7_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__7_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__8_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__7_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,13703464721909683084 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__8_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__8_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__9_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__8_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__20_value) as *mut crate::leanh::LeanObject,6617414847259481670 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__9_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__9_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__10_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__9_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__21_value) as *mut crate::leanh::LeanObject,1262856964488136044 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__10_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__10_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__11_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__10_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0_value) as *mut crate::leanh::LeanObject,9319191366458897102 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__11_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__11_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__12_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__12_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__12_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__13_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__11_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__12_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13836923486958114531 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__13_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__13_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__14_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__14_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__14_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__15_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__13_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__14_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15709648257435978966 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__15_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__15_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__16_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__15_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject,9455698986365397119 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__16_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__16_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__17_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__16_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__20_value) as *mut crate::leanh::LeanObject,11121705186153563937 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__17_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__17_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__18_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__17_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__21_value) as *mut crate::leanh::LeanObject,9401945981279613815 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__18_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__18_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__19_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__18_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__0_value) as *mut crate::leanh::LeanObject,13226874531422136977 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__19_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__19_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__21_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__21_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__21_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__23_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__23_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__23_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Elab_Deriving_Hashable_mkHashableHeader(
    mut v_indVal_2466_: *mut crate::leanh::LeanObject,
    mut v_a_2467_: *mut crate::leanh::LeanObject,
    mut v_a_2468_: *mut crate::leanh::LeanObject,
    mut v_a_2469_: *mut crate::leanh::LeanObject,
    mut v_a_2470_: *mut crate::leanh::LeanObject,
    mut v_a_2471_: *mut crate::leanh::LeanObject,
    mut v_a_2472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2474_ = l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1;
    v___x_2475_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2476_ = l_Lean_Elab_Deriving_mkHeader(
        v___x_2474_,
        v___x_2475_,
        v_indVal_2466_,
        v_a_2467_,
        v_a_2468_,
        v_a_2469_,
        v_a_2470_,
        v_a_2471_,
        v_a_2472_,
    );
    return v___x_2476_;
}
pub unsafe fn l_Lean_Elab_Deriving_Hashable_mkHashableHeader___boxed(
    mut v_indVal_2477_: *mut crate::leanh::LeanObject,
    mut v_a_2478_: *mut crate::leanh::LeanObject,
    mut v_a_2479_: *mut crate::leanh::LeanObject,
    mut v_a_2480_: *mut crate::leanh::LeanObject,
    mut v_a_2481_: *mut crate::leanh::LeanObject,
    mut v_a_2482_: *mut crate::leanh::LeanObject,
    mut v_a_2483_: *mut crate::leanh::LeanObject,
    mut v_a_2484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2485_ = l_Lean_Elab_Deriving_Hashable_mkHashableHeader(
        v_indVal_2477_,
        v_a_2478_,
        v_a_2479_,
        v_a_2480_,
        v_a_2481_,
        v_a_2482_,
        v_a_2483_,
    );
    crate::leanh::lean_dec(v_a_2483_);
    crate::leanh::lean_dec_ref(v_a_2482_);
    crate::leanh::lean_dec(v_a_2481_);
    crate::leanh::lean_dec_ref(v_a_2480_);
    crate::leanh::lean_dec(v_a_2479_);
    crate::leanh::lean_dec_ref(v_a_2478_);
    return v_res_2485_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0(
    mut v_k_2486_: *mut crate::leanh::LeanObject,
    mut v___y_2487_: *mut crate::leanh::LeanObject,
    mut v___y_2488_: *mut crate::leanh::LeanObject,
    mut v_b_2489_: *mut crate::leanh::LeanObject,
    mut v_c_2490_: *mut crate::leanh::LeanObject,
    mut v___y_2491_: *mut crate::leanh::LeanObject,
    mut v___y_2492_: *mut crate::leanh::LeanObject,
    mut v___y_2493_: *mut crate::leanh::LeanObject,
    mut v___y_2494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2494_);
    crate::leanh::lean_inc_ref(v___y_2493_);
    crate::leanh::lean_inc(v___y_2492_);
    crate::leanh::lean_inc_ref(v___y_2491_);
    crate::leanh::lean_inc(v___y_2488_);
    crate::leanh::lean_inc_ref(v___y_2487_);
    v___x_2496_ = crate::leanh::lean_apply_9(
        v_k_2486_,
        v_b_2489_,
        v_c_2490_,
        v___y_2487_,
        v___y_2488_,
        v___y_2491_,
        v___y_2492_,
        v___y_2493_,
        v___y_2494_,
        crate::leanh::lean_box(0),
    );
    return v___x_2496_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0___boxed(
    mut v_k_2497_: *mut crate::leanh::LeanObject,
    mut v___y_2498_: *mut crate::leanh::LeanObject,
    mut v___y_2499_: *mut crate::leanh::LeanObject,
    mut v_b_2500_: *mut crate::leanh::LeanObject,
    mut v_c_2501_: *mut crate::leanh::LeanObject,
    mut v___y_2502_: *mut crate::leanh::LeanObject,
    mut v___y_2503_: *mut crate::leanh::LeanObject,
    mut v___y_2504_: *mut crate::leanh::LeanObject,
    mut v___y_2505_: *mut crate::leanh::LeanObject,
    mut v___y_2506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2507_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0(v_k_2497_, v___y_2498_, v___y_2499_, v_b_2500_, v_c_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
    crate::leanh::lean_dec(v___y_2505_);
    crate::leanh::lean_dec_ref(v___y_2504_);
    crate::leanh::lean_dec(v___y_2503_);
    crate::leanh::lean_dec_ref(v___y_2502_);
    crate::leanh::lean_dec(v___y_2499_);
    crate::leanh::lean_dec_ref(v___y_2498_);
    return v_res_2507_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg(
    mut v_type_2508_: *mut crate::leanh::LeanObject,
    mut v_k_2509_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2510_: u8,
    mut v_whnfType_2511_: u8,
    mut v___y_2512_: *mut crate::leanh::LeanObject,
    mut v___y_2513_: *mut crate::leanh::LeanObject,
    mut v___y_2514_: *mut crate::leanh::LeanObject,
    mut v___y_2515_: *mut crate::leanh::LeanObject,
    mut v___y_2516_: *mut crate::leanh::LeanObject,
    mut v___y_2517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2524_: u8 = 0;
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_2513_);
                crate::leanh::lean_inc_ref(v___y_2512_);
                v___f_2519_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                crate::leanh::lean_closure_set(v___f_2519_, 0, v_k_2509_);
                crate::leanh::lean_closure_set(v___f_2519_, 1, v___y_2512_);
                crate::leanh::lean_closure_set(v___f_2519_, 2, v___y_2513_);
                v___x_2520_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    crate::leanh::lean_box(0),
                    v_type_2508_,
                    v___f_2519_,
                    v_cleanupAnnotations_2510_,
                    v_whnfType_2511_,
                    v___y_2514_,
                    v___y_2515_,
                    v___y_2516_,
                    v___y_2517_,
                );
                if crate::leanh::lean_obj_tag(v___x_2520_) == 0 {
                    return v___x_2520_;
                } else {
                    v_a_2521_ = crate::leanh::lean_ctor_get(v___x_2520_, 0);
                    v_isSharedCheck_2528_ = (!crate::leanh::lean_is_exclusive(v___x_2520_)) as u8;
                    if v_isSharedCheck_2528_ == 0 {
                        v___x_2523_ = v___x_2520_;
                        v_isShared_2524_ = v_isSharedCheck_2528_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2521_);
                        crate::leanh::lean_dec(v___x_2520_);
                        v___x_2523_ = crate::leanh::lean_box(0);
                        v_isShared_2524_ = v_isSharedCheck_2528_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2524_ == 0 {
                    v___x_2526_ = v___x_2523_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2527_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
                    v___x_2526_ = v_reuseFailAlloc_2527_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2526_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg___boxed(
    mut v_type_2529_: *mut crate::leanh::LeanObject,
    mut v_k_2530_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2531_: *mut crate::leanh::LeanObject,
    mut v_whnfType_2532_: *mut crate::leanh::LeanObject,
    mut v___y_2533_: *mut crate::leanh::LeanObject,
    mut v___y_2534_: *mut crate::leanh::LeanObject,
    mut v___y_2535_: *mut crate::leanh::LeanObject,
    mut v___y_2536_: *mut crate::leanh::LeanObject,
    mut v___y_2537_: *mut crate::leanh::LeanObject,
    mut v___y_2538_: *mut crate::leanh::LeanObject,
    mut v___y_2539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2540_: u8 = 0;
    let mut v_whnfType_boxed_2541_: u8 = 0;
    let mut v_res_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2540_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_2531_) as u8);
    v_whnfType_boxed_2541_ = (crate::leanh::lean_unbox(v_whnfType_2532_) as u8);
    v_res_2542_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg(v_type_2529_, v_k_2530_, v_cleanupAnnotations_boxed_2540_, v_whnfType_boxed_2541_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
    crate::leanh::lean_dec(v___y_2538_);
    crate::leanh::lean_dec_ref(v___y_2537_);
    crate::leanh::lean_dec(v___y_2536_);
    crate::leanh::lean_dec_ref(v___y_2535_);
    crate::leanh::lean_dec(v___y_2534_);
    crate::leanh::lean_dec_ref(v___y_2533_);
    return v_res_2542_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5(
    mut v_00_u03b1_2543_: *mut crate::leanh::LeanObject,
    mut v_type_2544_: *mut crate::leanh::LeanObject,
    mut v_k_2545_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2546_: u8,
    mut v_whnfType_2547_: u8,
    mut v___y_2548_: *mut crate::leanh::LeanObject,
    mut v___y_2549_: *mut crate::leanh::LeanObject,
    mut v___y_2550_: *mut crate::leanh::LeanObject,
    mut v___y_2551_: *mut crate::leanh::LeanObject,
    mut v___y_2552_: *mut crate::leanh::LeanObject,
    mut v___y_2553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2555_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg(v_type_2544_, v_k_2545_, v_cleanupAnnotations_2546_, v_whnfType_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
    return v___x_2555_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___boxed(
    mut v_00_u03b1_2556_: *mut crate::leanh::LeanObject,
    mut v_type_2557_: *mut crate::leanh::LeanObject,
    mut v_k_2558_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2559_: *mut crate::leanh::LeanObject,
    mut v_whnfType_2560_: *mut crate::leanh::LeanObject,
    mut v___y_2561_: *mut crate::leanh::LeanObject,
    mut v___y_2562_: *mut crate::leanh::LeanObject,
    mut v___y_2563_: *mut crate::leanh::LeanObject,
    mut v___y_2564_: *mut crate::leanh::LeanObject,
    mut v___y_2565_: *mut crate::leanh::LeanObject,
    mut v___y_2566_: *mut crate::leanh::LeanObject,
    mut v___y_2567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2568_: u8 = 0;
    let mut v_whnfType_boxed_2569_: u8 = 0;
    let mut v_res_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2568_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_2559_) as u8);
    v_whnfType_boxed_2569_ = (crate::leanh::lean_unbox(v_whnfType_2560_) as u8);
    v_res_2570_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5(v_00_u03b1_2556_, v_type_2557_, v_k_2558_, v_cleanupAnnotations_boxed_2568_, v_whnfType_boxed_2569_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
    crate::leanh::lean_dec(v___y_2566_);
    crate::leanh::lean_dec_ref(v___y_2565_);
    crate::leanh::lean_dec(v___y_2564_);
    crate::leanh::lean_dec_ref(v___y_2563_);
    crate::leanh::lean_dec(v___y_2562_);
    crate::leanh::lean_dec_ref(v___y_2561_);
    return v_res_2570_;
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2571_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_2571_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1(
    mut v_msg_2578_: *mut crate::leanh::LeanObject,
    mut v___y_2579_: *mut crate::leanh::LeanObject,
    mut v___y_2580_: *mut crate::leanh::LeanObject,
    mut v___y_2581_: *mut crate::leanh::LeanObject,
    mut v___y_2582_: *mut crate::leanh::LeanObject,
    mut v___y_2583_: *mut crate::leanh::LeanObject,
    mut v___y_2584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2591_: u8 = 0;
    let mut v_toFunctor_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2598_: u8 = 0;
    let mut v___f_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2615_: u8 = 0;
    let mut v_toFunctor_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2622_: u8 = 0;
    let mut v___f_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2639_: u8 = 0;
    let mut v_toFunctor_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2646_: u8 = 0;
    let mut v___f_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_30248__overap_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2665_: u8 = 0;
    let mut v_unused_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2667_: u8 = 0;
    let mut v_unused_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2671_: u8 = 0;
    let mut v_unused_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2673_: u8 = 0;
    let mut v_unused_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2677_: u8 = 0;
    let mut v_unused_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2679_: u8 = 0;
    let mut v_unused_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2586_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__0);
                v___x_2587_ = l_StateRefT_x27_instMonad___redArg(v___x_2586_);
                v_toApplicative_2588_ = crate::leanh::lean_ctor_get(v___x_2587_, 0);
                v_isSharedCheck_2679_ = (!crate::leanh::lean_is_exclusive(v___x_2587_)) as u8;
                if v_isSharedCheck_2679_ == 0 {
                    v_unused_2680_ = crate::leanh::lean_ctor_get(v___x_2587_, 1);
                    crate::leanh::lean_dec(v_unused_2680_);
                    v___x_2590_ = v___x_2587_;
                    v_isShared_2591_ = v_isSharedCheck_2679_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2588_);
                    crate::leanh::lean_dec(v___x_2587_);
                    v___x_2590_ = crate::leanh::lean_box(0);
                    v_isShared_2591_ = v_isSharedCheck_2679_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2592_ = crate::leanh::lean_ctor_get(v_toApplicative_2588_, 0);
                v_toSeq_2593_ = crate::leanh::lean_ctor_get(v_toApplicative_2588_, 2);
                v_toSeqLeft_2594_ = crate::leanh::lean_ctor_get(v_toApplicative_2588_, 3);
                v_toSeqRight_2595_ = crate::leanh::lean_ctor_get(v_toApplicative_2588_, 4);
                v_isSharedCheck_2677_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2588_)) as u8;
                if v_isSharedCheck_2677_ == 0 {
                    v_unused_2678_ = crate::leanh::lean_ctor_get(v_toApplicative_2588_, 1);
                    crate::leanh::lean_dec(v_unused_2678_);
                    v___x_2597_ = v_toApplicative_2588_;
                    v_isShared_2598_ = v_isSharedCheck_2677_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2595_);
                    crate::leanh::lean_inc(v_toSeqLeft_2594_);
                    crate::leanh::lean_inc(v_toSeq_2593_);
                    crate::leanh::lean_inc(v_toFunctor_2592_);
                    crate::leanh::lean_dec(v_toApplicative_2588_);
                    v___x_2597_ = crate::leanh::lean_box(0);
                    v_isShared_2598_ = v_isSharedCheck_2677_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2599_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__1;
                v___f_2600_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_2592_);
                v___f_2601_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2601_, 0, v_toFunctor_2592_);
                v___f_2602_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2602_, 0, v_toFunctor_2592_);
                v___x_2603_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2603_, 0, v___f_2601_);
                crate::leanh::lean_ctor_set(v___x_2603_, 1, v___f_2602_);
                v___f_2604_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2604_, 0, v_toSeqRight_2595_);
                v___f_2605_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2605_, 0, v_toSeqLeft_2594_);
                v___f_2606_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2606_, 0, v_toSeq_2593_);
                if v_isShared_2598_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2597_, 4, v___f_2604_);
                    crate::leanh::lean_ctor_set(v___x_2597_, 3, v___f_2605_);
                    crate::leanh::lean_ctor_set(v___x_2597_, 2, v___f_2606_);
                    crate::leanh::lean_ctor_set(v___x_2597_, 1, v___f_2599_);
                    crate::leanh::lean_ctor_set(v___x_2597_, 0, v___x_2603_);
                    v___x_2608_ = v___x_2597_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2676_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2603_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2676_, 1, v___f_2599_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2676_, 2, v___f_2606_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2676_, 3, v___f_2605_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2676_, 4, v___f_2604_);
                    v___x_2608_ = v_reuseFailAlloc_2676_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2591_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2590_, 1, v___f_2600_);
                    crate::leanh::lean_ctor_set(v___x_2590_, 0, v___x_2608_);
                    v___x_2610_ = v___x_2590_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2675_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2608_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2675_, 1, v___f_2600_);
                    v___x_2610_ = v_reuseFailAlloc_2675_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2611_ = l_StateRefT_x27_instMonad___redArg(v___x_2610_);
                v_toApplicative_2612_ = crate::leanh::lean_ctor_get(v___x_2611_, 0);
                v_isSharedCheck_2673_ = (!crate::leanh::lean_is_exclusive(v___x_2611_)) as u8;
                if v_isSharedCheck_2673_ == 0 {
                    v_unused_2674_ = crate::leanh::lean_ctor_get(v___x_2611_, 1);
                    crate::leanh::lean_dec(v_unused_2674_);
                    v___x_2614_ = v___x_2611_;
                    v_isShared_2615_ = v_isSharedCheck_2673_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2612_);
                    crate::leanh::lean_dec(v___x_2611_);
                    v___x_2614_ = crate::leanh::lean_box(0);
                    v_isShared_2615_ = v_isSharedCheck_2673_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_2616_ = crate::leanh::lean_ctor_get(v_toApplicative_2612_, 0);
                v_toSeq_2617_ = crate::leanh::lean_ctor_get(v_toApplicative_2612_, 2);
                v_toSeqLeft_2618_ = crate::leanh::lean_ctor_get(v_toApplicative_2612_, 3);
                v_toSeqRight_2619_ = crate::leanh::lean_ctor_get(v_toApplicative_2612_, 4);
                v_isSharedCheck_2671_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2612_)) as u8;
                if v_isSharedCheck_2671_ == 0 {
                    v_unused_2672_ = crate::leanh::lean_ctor_get(v_toApplicative_2612_, 1);
                    crate::leanh::lean_dec(v_unused_2672_);
                    v___x_2621_ = v_toApplicative_2612_;
                    v_isShared_2622_ = v_isSharedCheck_2671_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2619_);
                    crate::leanh::lean_inc(v_toSeqLeft_2618_);
                    crate::leanh::lean_inc(v_toSeq_2617_);
                    crate::leanh::lean_inc(v_toFunctor_2616_);
                    crate::leanh::lean_dec(v_toApplicative_2612_);
                    v___x_2621_ = crate::leanh::lean_box(0);
                    v_isShared_2622_ = v_isSharedCheck_2671_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_2623_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__3;
                v___f_2624_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_2616_);
                v___f_2625_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2625_, 0, v_toFunctor_2616_);
                v___f_2626_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2626_, 0, v_toFunctor_2616_);
                v___x_2627_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2627_, 0, v___f_2625_);
                crate::leanh::lean_ctor_set(v___x_2627_, 1, v___f_2626_);
                v___f_2628_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2628_, 0, v_toSeqRight_2619_);
                v___f_2629_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2629_, 0, v_toSeqLeft_2618_);
                v___f_2630_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2630_, 0, v_toSeq_2617_);
                if v_isShared_2622_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2621_, 4, v___f_2628_);
                    crate::leanh::lean_ctor_set(v___x_2621_, 3, v___f_2629_);
                    crate::leanh::lean_ctor_set(v___x_2621_, 2, v___f_2630_);
                    crate::leanh::lean_ctor_set(v___x_2621_, 1, v___f_2623_);
                    crate::leanh::lean_ctor_set(v___x_2621_, 0, v___x_2627_);
                    v___x_2632_ = v___x_2621_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2670_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2627_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2670_, 1, v___f_2623_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2670_, 2, v___f_2630_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2670_, 3, v___f_2629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2670_, 4, v___f_2628_);
                    v___x_2632_ = v_reuseFailAlloc_2670_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2615_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2614_, 1, v___f_2624_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 0, v___x_2632_);
                    v___x_2634_ = v___x_2614_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2669_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2669_, 1, v___f_2624_);
                    v___x_2634_ = v_reuseFailAlloc_2669_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2635_ = l_StateRefT_x27_instMonad___redArg(v___x_2634_);
                v_toApplicative_2636_ = crate::leanh::lean_ctor_get(v___x_2635_, 0);
                v_isSharedCheck_2667_ = (!crate::leanh::lean_is_exclusive(v___x_2635_)) as u8;
                if v_isSharedCheck_2667_ == 0 {
                    v_unused_2668_ = crate::leanh::lean_ctor_get(v___x_2635_, 1);
                    crate::leanh::lean_dec(v_unused_2668_);
                    v___x_2638_ = v___x_2635_;
                    v_isShared_2639_ = v_isSharedCheck_2667_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2636_);
                    crate::leanh::lean_dec(v___x_2635_);
                    v___x_2638_ = crate::leanh::lean_box(0);
                    v_isShared_2639_ = v_isSharedCheck_2667_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_toFunctor_2640_ = crate::leanh::lean_ctor_get(v_toApplicative_2636_, 0);
                v_toSeq_2641_ = crate::leanh::lean_ctor_get(v_toApplicative_2636_, 2);
                v_toSeqLeft_2642_ = crate::leanh::lean_ctor_get(v_toApplicative_2636_, 3);
                v_toSeqRight_2643_ = crate::leanh::lean_ctor_get(v_toApplicative_2636_, 4);
                v_isSharedCheck_2665_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2636_)) as u8;
                if v_isSharedCheck_2665_ == 0 {
                    v_unused_2666_ = crate::leanh::lean_ctor_get(v_toApplicative_2636_, 1);
                    crate::leanh::lean_dec(v_unused_2666_);
                    v___x_2645_ = v_toApplicative_2636_;
                    v_isShared_2646_ = v_isSharedCheck_2665_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2643_);
                    crate::leanh::lean_inc(v_toSeqLeft_2642_);
                    crate::leanh::lean_inc(v_toSeq_2641_);
                    crate::leanh::lean_inc(v_toFunctor_2640_);
                    crate::leanh::lean_dec(v_toApplicative_2636_);
                    v___x_2645_ = crate::leanh::lean_box(0);
                    v_isShared_2646_ = v_isSharedCheck_2665_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___f_2647_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__5;
                v___f_2648_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___closed__6;
                crate::leanh::lean_inc_ref(v_toFunctor_2640_);
                v___f_2649_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2649_, 0, v_toFunctor_2640_);
                v___f_2650_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2650_, 0, v_toFunctor_2640_);
                v___x_2651_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2651_, 0, v___f_2649_);
                crate::leanh::lean_ctor_set(v___x_2651_, 1, v___f_2650_);
                v___f_2652_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2652_, 0, v_toSeqRight_2643_);
                v___f_2653_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2653_, 0, v_toSeqLeft_2642_);
                v___f_2654_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2654_, 0, v_toSeq_2641_);
                if v_isShared_2646_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2645_, 4, v___f_2652_);
                    crate::leanh::lean_ctor_set(v___x_2645_, 3, v___f_2653_);
                    crate::leanh::lean_ctor_set(v___x_2645_, 2, v___f_2654_);
                    crate::leanh::lean_ctor_set(v___x_2645_, 1, v___f_2647_);
                    crate::leanh::lean_ctor_set(v___x_2645_, 0, v___x_2651_);
                    v___x_2656_ = v___x_2645_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2664_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2651_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 1, v___f_2647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 2, v___f_2654_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 3, v___f_2653_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 4, v___f_2652_);
                    v___x_2656_ = v_reuseFailAlloc_2664_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2639_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2638_, 1, v___f_2648_);
                    crate::leanh::lean_ctor_set(v___x_2638_, 0, v___x_2656_);
                    v___x_2658_ = v___x_2638_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2663_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2656_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2663_, 1, v___f_2648_);
                    v___x_2658_ = v_reuseFailAlloc_2663_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2659_ = crate::leanh::lean_box(0);
                v___x_2660_ = l_instInhabitedOfMonad___redArg(v___x_2658_, v___x_2659_);
                v___x_30248__overap_2661_ = lean_panic_fn_borrowed(v___x_2660_, v_msg_2578_);
                crate::leanh::lean_dec(v___x_2660_);
                crate::leanh::lean_inc(v___y_2584_);
                crate::leanh::lean_inc_ref(v___y_2583_);
                crate::leanh::lean_inc(v___y_2582_);
                crate::leanh::lean_inc_ref(v___y_2581_);
                crate::leanh::lean_inc(v___y_2580_);
                crate::leanh::lean_inc_ref(v___y_2579_);
                v___x_2662_ = crate::leanh::lean_apply_7(
                    v___x_30248__overap_2661_,
                    v___y_2579_,
                    v___y_2580_,
                    v___y_2581_,
                    v___y_2582_,
                    v___y_2583_,
                    v___y_2584_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2662_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1___boxed(
    mut v_msg_2681_: *mut crate::leanh::LeanObject,
    mut v___y_2682_: *mut crate::leanh::LeanObject,
    mut v___y_2683_: *mut crate::leanh::LeanObject,
    mut v___y_2684_: *mut crate::leanh::LeanObject,
    mut v___y_2685_: *mut crate::leanh::LeanObject,
    mut v___y_2686_: *mut crate::leanh::LeanObject,
    mut v___y_2687_: *mut crate::leanh::LeanObject,
    mut v___y_2688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2689_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1(v_msg_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
    crate::leanh::lean_dec(v___y_2687_);
    crate::leanh::lean_dec_ref(v___y_2686_);
    crate::leanh::lean_dec(v___y_2685_);
    crate::leanh::lean_dec_ref(v___y_2684_);
    crate::leanh::lean_dec(v___y_2683_);
    crate::leanh::lean_dec_ref(v___y_2682_);
    return v_res_2689_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2(
    mut v_msgData_2690_: *mut crate::leanh::LeanObject,
    mut v___y_2691_: *mut crate::leanh::LeanObject,
    mut v___y_2692_: *mut crate::leanh::LeanObject,
    mut v___y_2693_: *mut crate::leanh::LeanObject,
    mut v___y_2694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2696_ = lean_st_ref_get(v___y_2694_);
    v_env_2697_ = crate::leanh::lean_ctor_get(v___x_2696_, 0);
    crate::leanh::lean_inc_ref(v_env_2697_);
    crate::leanh::lean_dec(v___x_2696_);
    v___x_2698_ = lean_st_ref_get(v___y_2692_);
    v_mctx_2699_ = crate::leanh::lean_ctor_get(v___x_2698_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2699_);
    crate::leanh::lean_dec(v___x_2698_);
    v_lctx_2700_ = crate::leanh::lean_ctor_get(v___y_2691_, 2);
    v_options_2701_ = crate::leanh::lean_ctor_get(v___y_2693_, 2);
    crate::leanh::lean_inc_ref(v_options_2701_);
    crate::leanh::lean_inc_ref(v_lctx_2700_);
    v___x_2702_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2702_, 0, v_env_2697_);
    crate::leanh::lean_ctor_set(v___x_2702_, 1, v_mctx_2699_);
    crate::leanh::lean_ctor_set(v___x_2702_, 2, v_lctx_2700_);
    crate::leanh::lean_ctor_set(v___x_2702_, 3, v_options_2701_);
    v___x_2703_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2703_, 0, v___x_2702_);
    crate::leanh::lean_ctor_set(v___x_2703_, 1, v_msgData_2690_);
    v___x_2704_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2704_, 0, v___x_2703_);
    return v___x_2704_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2___boxed(
    mut v_msgData_2705_: *mut crate::leanh::LeanObject,
    mut v___y_2706_: *mut crate::leanh::LeanObject,
    mut v___y_2707_: *mut crate::leanh::LeanObject,
    mut v___y_2708_: *mut crate::leanh::LeanObject,
    mut v___y_2709_: *mut crate::leanh::LeanObject,
    mut v___y_2710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2711_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2(v_msgData_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
    crate::leanh::lean_dec(v___y_2709_);
    crate::leanh::lean_dec_ref(v___y_2708_);
    crate::leanh::lean_dec(v___y_2707_);
    crate::leanh::lean_dec_ref(v___y_2706_);
    return v_res_2711_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2712_ = crate::leanh::lean_box(1);
    v___x_2713_ = l_Lean_MessageData_ofFormat(v___x_2712_);
    return v___x_2713_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2717_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__2;
    v___x_2718_ = l_Lean_MessageData_ofFormat(v___x_2717_);
    return v___x_2718_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12(
    mut v_x_2719_: *mut crate::leanh::LeanObject,
    mut v_x_2720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2725_: u8 = 0;
    let mut v_before_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2729_: u8 = 0;
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2742_: u8 = 0;
    let mut v_unused_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2744_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2720_) == 0 {
                    return v_x_2719_;
                } else {
                    v_head_2721_ = crate::leanh::lean_ctor_get(v_x_2720_, 0);
                    v_tail_2722_ = crate::leanh::lean_ctor_get(v_x_2720_, 1);
                    v_isSharedCheck_2744_ = (!crate::leanh::lean_is_exclusive(v_x_2720_)) as u8;
                    if v_isSharedCheck_2744_ == 0 {
                        v___x_2724_ = v_x_2720_;
                        v_isShared_2725_ = v_isSharedCheck_2744_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2722_);
                        crate::leanh::lean_inc(v_head_2721_);
                        crate::leanh::lean_dec(v_x_2720_);
                        v___x_2724_ = crate::leanh::lean_box(0);
                        v_isShared_2725_ = v_isSharedCheck_2744_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_2726_ = crate::leanh::lean_ctor_get(v_head_2721_, 0);
                v_isSharedCheck_2742_ = (!crate::leanh::lean_is_exclusive(v_head_2721_)) as u8;
                if v_isSharedCheck_2742_ == 0 {
                    v_unused_2743_ = crate::leanh::lean_ctor_get(v_head_2721_, 1);
                    crate::leanh::lean_dec(v_unused_2743_);
                    v___x_2728_ = v_head_2721_;
                    v_isShared_2729_ = v_isSharedCheck_2742_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_2726_);
                    crate::leanh::lean_dec(v_head_2721_);
                    v___x_2728_ = crate::leanh::lean_box(0);
                    v_isShared_2729_ = v_isSharedCheck_2742_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2730_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0);
                if v_isShared_2729_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2728_, 7);
                    crate::leanh::lean_ctor_set(v___x_2728_, 1, v___x_2730_);
                    crate::leanh::lean_ctor_set(v___x_2728_, 0, v_x_2719_);
                    v___x_2732_ = v___x_2728_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2741_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_x_2719_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2741_, 1, v___x_2730_);
                    v___x_2732_ = v_reuseFailAlloc_2741_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2733_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3);
                if v_isShared_2725_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2724_, 7);
                    crate::leanh::lean_ctor_set(v___x_2724_, 1, v___x_2733_);
                    crate::leanh::lean_ctor_set(v___x_2724_, 0, v___x_2732_);
                    v___x_2735_ = v___x_2724_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2740_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2732_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2740_, 1, v___x_2733_);
                    v___x_2735_ = v_reuseFailAlloc_2740_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2736_ = l_Lean_MessageData_ofSyntax(v_before_2726_);
                v___x_2737_ = l_Lean_indentD(v___x_2736_);
                v___x_2738_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2738_, 0, v___x_2735_);
                crate::leanh::lean_ctor_set(v___x_2738_, 1, v___x_2737_);
                v_x_2719_ = v___x_2738_;
                v_x_2720_ = v_tail_2722_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11(
    mut v_opts_2745_: *mut crate::leanh::LeanObject,
    mut v_opt_2746_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2747_ = crate::leanh::lean_ctor_get(v_opt_2746_, 0);
    v_defValue_2748_ = crate::leanh::lean_ctor_get(v_opt_2746_, 1);
    v_map_2749_ = crate::leanh::lean_ctor_get(v_opts_2745_, 0);
    v___x_2750_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2749_,
            v_name_2747_,
        );
    if crate::leanh::lean_obj_tag(v___x_2750_) == 0 {
        let mut v___x_2751_: u8 = 0;
        v___x_2751_ = (crate::leanh::lean_unbox(v_defValue_2748_) as u8);
        return v___x_2751_;
    } else {
        let mut v_val_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2752_ = crate::leanh::lean_ctor_get(v___x_2750_, 0);
        crate::leanh::lean_inc(v_val_2752_);
        crate::leanh::lean_dec_ref_known(v___x_2750_, 1);
        if crate::leanh::lean_obj_tag(v_val_2752_) == 1 {
            let mut v_v_2753_: u8 = 0;
            v_v_2753_ = crate::leanh::lean_ctor_get_uint8(v_val_2752_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_2752_, 0);
            return v_v_2753_;
        } else {
            let mut v___x_2754_: u8 = 0;
            crate::leanh::lean_dec(v_val_2752_);
            v___x_2754_ = (crate::leanh::lean_unbox(v_defValue_2748_) as u8);
            return v___x_2754_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11___boxed(
    mut v_opts_2755_: *mut crate::leanh::LeanObject,
    mut v_opt_2756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2757_: u8 = 0;
    let mut v_r_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2757_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11(v_opts_2755_, v_opt_2756_);
    crate::leanh::lean_dec_ref(v_opt_2756_);
    crate::leanh::lean_dec_ref(v_opts_2755_);
    v_r_2758_ = crate::leanh::lean_box((v_res_2757_) as usize);
    return v_r_2758_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2762_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1;
    v___x_2763_ = l_Lean_MessageData_ofFormat(v___x_2762_);
    return v___x_2763_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg(
    mut v_msgData_2764_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2765_: *mut crate::leanh::LeanObject,
    mut v___y_2766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: u8 = 0;
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2777_: u8 = 0;
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2789_: u8 = 0;
    let mut v_unused_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2768_ = crate::leanh::lean_ctor_get(v___y_2766_, 2);
                v___x_2769_ = l_Lean_Elab_pp_macroStack;
                v___x_2770_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__11(v_options_2768_, v___x_2769_);
                if v___x_2770_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_2765_);
                    v___x_2771_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2771_, 0, v_msgData_2764_);
                    return v___x_2771_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_2765_) == 0 {
                        v___x_2772_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2772_, 0, v_msgData_2764_);
                        return v___x_2772_;
                    } else {
                        v_head_2773_ = crate::leanh::lean_ctor_get(v_macroStack_2765_, 0);
                        crate::leanh::lean_inc(v_head_2773_);
                        v_after_2774_ = crate::leanh::lean_ctor_get(v_head_2773_, 1);
                        v_isSharedCheck_2789_ =
                            (!crate::leanh::lean_is_exclusive(v_head_2773_)) as u8;
                        if v_isSharedCheck_2789_ == 0 {
                            v_unused_2790_ = crate::leanh::lean_ctor_get(v_head_2773_, 0);
                            crate::leanh::lean_dec(v_unused_2790_);
                            v___x_2776_ = v_head_2773_;
                            v_isShared_2777_ = v_isSharedCheck_2789_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_2774_);
                            crate::leanh::lean_dec(v_head_2773_);
                            v___x_2776_ = crate::leanh::lean_box(0);
                            v_isShared_2777_ = v_isSharedCheck_2789_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2778_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0);
                if v_isShared_2777_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2776_, 7);
                    crate::leanh::lean_ctor_set(v___x_2776_, 1, v___x_2778_);
                    crate::leanh::lean_ctor_set(v___x_2776_, 0, v_msgData_2764_);
                    v___x_2780_ = v___x_2776_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2788_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_msgData_2764_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2788_, 1, v___x_2778_);
                    v___x_2780_ = v_reuseFailAlloc_2788_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2781_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
                v___x_2782_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2782_, 0, v___x_2780_);
                crate::leanh::lean_ctor_set(v___x_2782_, 1, v___x_2781_);
                v___x_2783_ = l_Lean_MessageData_ofSyntax(v_after_2774_);
                v___x_2784_ = l_Lean_indentD(v___x_2783_);
                v_msgData_2785_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_2785_, 0, v___x_2782_);
                crate::leanh::lean_ctor_set(v_msgData_2785_, 1, v___x_2784_);
                v___x_2786_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3_spec__12(v_msgData_2785_, v_macroStack_2765_);
                v___x_2787_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2787_, 0, v___x_2786_);
                return v___x_2787_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_msgData_2791_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2792_: *mut crate::leanh::LeanObject,
    mut v___y_2793_: *mut crate::leanh::LeanObject,
    mut v___y_2794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2795_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_2791_, v_macroStack_2792_, v___y_2793_);
    crate::leanh::lean_dec_ref(v___y_2793_);
    return v_res_2795_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg(
    mut v_msg_2796_: *mut crate::leanh::LeanObject,
    mut v___y_2797_: *mut crate::leanh::LeanObject,
    mut v___y_2798_: *mut crate::leanh::LeanObject,
    mut v___y_2799_: *mut crate::leanh::LeanObject,
    mut v___y_2800_: *mut crate::leanh::LeanObject,
    mut v___y_2801_: *mut crate::leanh::LeanObject,
    mut v___y_2802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2813_: u8 = 0;
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2818_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2804_ = crate::leanh::lean_ctor_get(v___y_2801_, 5);
                v___x_2805_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2(v_msg_2796_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
                v_a_2806_ = crate::leanh::lean_ctor_get(v___x_2805_, 0);
                crate::leanh::lean_inc(v_a_2806_);
                crate::leanh::lean_dec_ref(v___x_2805_);
                v_macroStack_2807_ = crate::leanh::lean_ctor_get(v___y_2797_, 1);
                v___x_2808_ = l_Lean_Elab_getBetterRef(v_ref_2804_, v_macroStack_2807_);
                crate::leanh::lean_inc(v_macroStack_2807_);
                v___x_2809_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg(v_a_2806_, v_macroStack_2807_, v___y_2801_);
                v_a_2810_ = crate::leanh::lean_ctor_get(v___x_2809_, 0);
                v_isSharedCheck_2818_ = (!crate::leanh::lean_is_exclusive(v___x_2809_)) as u8;
                if v_isSharedCheck_2818_ == 0 {
                    v___x_2812_ = v___x_2809_;
                    v_isShared_2813_ = v_isSharedCheck_2818_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2810_);
                    crate::leanh::lean_dec(v___x_2809_);
                    v___x_2812_ = crate::leanh::lean_box(0);
                    v_isShared_2813_ = v_isSharedCheck_2818_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2814_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2814_, 0, v___x_2808_);
                crate::leanh::lean_ctor_set(v___x_2814_, 1, v_a_2810_);
                if v_isShared_2813_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2812_, 1);
                    crate::leanh::lean_ctor_set(v___x_2812_, 0, v___x_2814_);
                    v___x_2816_ = v___x_2812_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2817_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2814_);
                    v___x_2816_ = v_reuseFailAlloc_2817_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2816_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg___boxed(
    mut v_msg_2819_: *mut crate::leanh::LeanObject,
    mut v___y_2820_: *mut crate::leanh::LeanObject,
    mut v___y_2821_: *mut crate::leanh::LeanObject,
    mut v___y_2822_: *mut crate::leanh::LeanObject,
    mut v___y_2823_: *mut crate::leanh::LeanObject,
    mut v___y_2824_: *mut crate::leanh::LeanObject,
    mut v___y_2825_: *mut crate::leanh::LeanObject,
    mut v___y_2826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2827_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg(v_msg_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
    crate::leanh::lean_dec(v___y_2825_);
    crate::leanh::lean_dec_ref(v___y_2824_);
    crate::leanh::lean_dec(v___y_2823_);
    crate::leanh::lean_dec_ref(v___y_2822_);
    crate::leanh::lean_dec(v___y_2821_);
    crate::leanh::lean_dec_ref(v___y_2820_);
    return v_res_2827_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2829_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__0;
    v___x_2830_ = l_Lean_stringToMessageData(v___x_2829_);
    return v___x_2830_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2832_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__2;
    v___x_2833_ = l_Lean_stringToMessageData(v___x_2832_);
    return v___x_2833_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2837_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__6;
    v___x_2838_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_2839_ = crate::leanh::lean_unsigned_to_nat(122);
    v___x_2840_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__5;
    v___x_2841_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__4;
    v___x_2842_ = l_mkPanicMessageWithDecl(
        v___x_2841_,
        v___x_2840_,
        v___x_2839_,
        v___x_2838_,
        v___x_2837_,
    );
    return v___x_2842_;
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0(
    mut v_constName_2843_: *mut crate::leanh::LeanObject,
    mut v___y_2844_: *mut crate::leanh::LeanObject,
    mut v___y_2845_: *mut crate::leanh::LeanObject,
    mut v___y_2846_: *mut crate::leanh::LeanObject,
    mut v___y_2847_: *mut crate::leanh::LeanObject,
    mut v___y_2848_: *mut crate::leanh::LeanObject,
    mut v___y_2849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: u8 = 0;
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: u8 = 0;
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2864_: u8 = 0;
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2869_: u8 = 0;
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2873_: u8 = 0;
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2879_: u8 = 0;
    let mut v_val_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2884_: u8 = 0;
    let mut v_a_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2888_: u8 = 0;
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2892_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2859_ = lean_st_ref_get(v___y_2849_);
                v_env_2860_ = crate::leanh::lean_ctor_get(v___x_2859_, 0);
                crate::leanh::lean_inc_ref(v_env_2860_);
                crate::leanh::lean_dec(v___x_2859_);
                v___x_2861_ = 0;
                crate::leanh::lean_inc(v_constName_2843_);
                v___x_2862_ =
                    l_Lean_Environment_findAsync_x3f(v_env_2860_, v_constName_2843_, v___x_2861_);
                if crate::leanh::lean_obj_tag(v___x_2862_) == 1 {
                    v_val_2863_ = crate::leanh::lean_ctor_get(v___x_2862_, 0);
                    crate::leanh::lean_inc(v_val_2863_);
                    crate::leanh::lean_dec_ref_known(v___x_2862_, 1);
                    v_kind_2864_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_2863_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    if v_kind_2864_ == 6 {
                        v___x_2865_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2863_);
                        if crate::leanh::lean_obj_tag(v___x_2865_) == 6 {
                            crate::leanh::lean_dec(v_constName_2843_);
                            v_val_2866_ = crate::leanh::lean_ctor_get(v___x_2865_, 0);
                            v_isSharedCheck_2873_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2865_)) as u8;
                            if v_isSharedCheck_2873_ == 0 {
                                v___x_2868_ = v___x_2865_;
                                v_isShared_2869_ = v_isSharedCheck_2873_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_2866_);
                                crate::leanh::lean_dec(v___x_2865_);
                                v___x_2868_ = crate::leanh::lean_box(0);
                                v_isShared_2869_ = v_isSharedCheck_2873_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2865_);
                            v___x_2874_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7_once), _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__7);
                            v___x_2875_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__1(v___x_2874_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
                            if crate::leanh::lean_obj_tag(v___x_2875_) == 0 {
                                v_a_2876_ = crate::leanh::lean_ctor_get(v___x_2875_, 0);
                                v_isSharedCheck_2884_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2875_)) as u8;
                                if v_isSharedCheck_2884_ == 0 {
                                    v___x_2878_ = v___x_2875_;
                                    v_isShared_2879_ = v_isSharedCheck_2884_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2876_);
                                    crate::leanh::lean_dec(v___x_2875_);
                                    v___x_2878_ = crate::leanh::lean_box(0);
                                    v_isShared_2879_ = v_isSharedCheck_2884_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_constName_2843_);
                                v_a_2885_ = crate::leanh::lean_ctor_get(v___x_2875_, 0);
                                v_isSharedCheck_2892_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2875_)) as u8;
                                if v_isSharedCheck_2892_ == 0 {
                                    v___x_2887_ = v___x_2875_;
                                    v_isShared_2888_ = v_isSharedCheck_2892_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2885_);
                                    crate::leanh::lean_dec(v___x_2875_);
                                    v___x_2887_ = crate::leanh::lean_box(0);
                                    v_isShared_2888_ = v_isSharedCheck_2892_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_2863_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2862_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2852_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__1);
                v___x_2853_ = 0;
                v___x_2854_ = l_Lean_MessageData_ofConstName(v_constName_2843_, v___x_2853_);
                v___x_2855_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2855_, 0, v___x_2852_);
                crate::leanh::lean_ctor_set(v___x_2855_, 1, v___x_2854_);
                v___x_2856_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3_once), _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___closed__3);
                v___x_2857_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2857_, 0, v___x_2855_);
                crate::leanh::lean_ctor_set(v___x_2857_, 1, v___x_2856_);
                v___x_2858_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg(v___x_2857_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
                return v___x_2858_;
            }
            2 => {
                if v_isShared_2869_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2868_, 0);
                    v___x_2871_ = v___x_2868_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2872_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_val_2866_);
                    v___x_2871_ = v_reuseFailAlloc_2872_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2871_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_2876_) == 0 {
                    crate::leanh::lean_del_object(v___x_2878_);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_constName_2843_);
                    v_val_2880_ = crate::leanh::lean_ctor_get(v_a_2876_, 0);
                    crate::leanh::lean_inc(v_val_2880_);
                    crate::leanh::lean_dec_ref_known(v_a_2876_, 1);
                    if v_isShared_2879_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2878_, 0, v_val_2880_);
                        v___x_2882_ = v___x_2878_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2883_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_val_2880_);
                        v___x_2882_ = v_reuseFailAlloc_2883_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_2882_;
            }
            6 => {
                if v_isShared_2888_ == 0 {
                    v___x_2890_ = v___x_2887_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2891_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
                    v___x_2890_ = v_reuseFailAlloc_2891_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2890_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0___boxed(
    mut v_constName_2893_: *mut crate::leanh::LeanObject,
    mut v___y_2894_: *mut crate::leanh::LeanObject,
    mut v___y_2895_: *mut crate::leanh::LeanObject,
    mut v___y_2896_: *mut crate::leanh::LeanObject,
    mut v___y_2897_: *mut crate::leanh::LeanObject,
    mut v___y_2898_: *mut crate::leanh::LeanObject,
    mut v___y_2899_: *mut crate::leanh::LeanObject,
    mut v___y_2900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2901_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0(v_constName_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
    crate::leanh::lean_dec(v___y_2899_);
    crate::leanh::lean_dec_ref(v___y_2898_);
    crate::leanh::lean_dec(v___y_2897_);
    crate::leanh::lean_dec_ref(v___y_2896_);
    crate::leanh::lean_dec(v___y_2895_);
    crate::leanh::lean_dec_ref(v___y_2894_);
    return v_res_2901_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1(
    mut v_sz_2902_: usize,
    mut v_i_2903_: usize,
    mut v_bs_2904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2905_: u8 = 0;
    let mut v_v_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: usize = 0;
    let mut v___x_2910_: usize = 0;
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2905_ = lean_usize_dec_lt(v_i_2903_, v_sz_2902_);
                if v___x_2905_ == 0 {
                    return v_bs_2904_;
                } else {
                    v_v_2906_ = lean_array_uget(v_bs_2904_, v_i_2903_);
                    v___x_2907_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2908_ = lean_array_uset(v_bs_2904_, v_i_2903_, v___x_2907_);
                    v___x_2909_ = 1usize;
                    v___x_2910_ = lean_usize_add(v_i_2903_, v___x_2909_);
                    v___x_2911_ = lean_array_uset(v_bs_x27_2908_, v_i_2903_, v_v_2906_);
                    v_i_2903_ = v___x_2910_;
                    v_bs_2904_ = v___x_2911_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1___boxed(
    mut v_sz_2913_: *mut crate::leanh::LeanObject,
    mut v_i_2914_: *mut crate::leanh::LeanObject,
    mut v_bs_2915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2916_: usize = 0;
    let mut v_i_boxed_2917_: usize = 0;
    let mut v_res_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2916_ = crate::leanh::lean_unbox_usize(v_sz_2913_);
    crate::leanh::lean_dec(v_sz_2913_);
    v_i_boxed_2917_ = crate::leanh::lean_unbox_usize(v_i_2914_);
    crate::leanh::lean_dec(v_i_2914_);
    v_res_2918_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1(v_sz_boxed_2916_, v_i_boxed_2917_, v_bs_2915_);
    return v_res_2918_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(
    mut v_upperBound_2929_: *mut crate::leanh::LeanObject,
    mut v_a_2930_: *mut crate::leanh::LeanObject,
    mut v_b_2931_: *mut crate::leanh::LeanObject,
    mut v___y_2932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2934_: u8 = 0;
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: u8 = 0;
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2934_ = lean_nat_dec_lt(v_a_2930_, v_upperBound_2929_);
                if v___x_2934_ == 0 {
                    crate::leanh::lean_dec(v_a_2930_);
                    v___x_2935_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2935_, 0, v_b_2931_);
                    return v___x_2935_;
                } else {
                    v_ref_2936_ = crate::leanh::lean_ctor_get(v___y_2932_, 5);
                    v___x_2937_ = 0;
                    v___x_2938_ = l_Lean_SourceInfo_fromRef(v_ref_2936_, v___x_2937_);
                    v___x_2939_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__4;
                    v___x_2940_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___closed__5;
                    crate::leanh::lean_inc(v___x_2938_);
                    v___x_2941_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2941_, 0, v___x_2938_);
                    crate::leanh::lean_ctor_set(v___x_2941_, 1, v___x_2940_);
                    v___x_2942_ = l_Lean_Syntax_node1(v___x_2938_, v___x_2939_, v___x_2941_);
                    v___x_2943_ = lean_array_push(v_b_2931_, v___x_2942_);
                    v___x_2944_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2945_ = lean_nat_add(v_a_2930_, v___x_2944_);
                    crate::leanh::lean_dec(v_a_2930_);
                    v_a_2930_ = v___x_2945_;
                    v_b_2931_ = v___x_2943_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg___boxed(
    mut v_upperBound_2947_: *mut crate::leanh::LeanObject,
    mut v_a_2948_: *mut crate::leanh::LeanObject,
    mut v_b_2949_: *mut crate::leanh::LeanObject,
    mut v___y_2950_: *mut crate::leanh::LeanObject,
    mut v___y_2951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2952_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(v_upperBound_2947_, v_a_2948_, v_b_2949_, v___y_2950_);
    crate::leanh::lean_dec_ref(v___y_2950_);
    crate::leanh::lean_dec(v_upperBound_2947_);
    return v_res_2952_;
}
pub unsafe fn l_Array_findIdx_x3f_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2(
    mut v_declName_2953_: *mut crate::leanh::LeanObject,
    mut v_as_2954_: *mut crate::leanh::LeanObject,
    mut v_j_2955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: u8 = 0;
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: u8 = 0;
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2956_ = lean_array_get_size(v_as_2954_);
                v___x_2957_ = lean_nat_dec_lt(v_j_2955_, v___x_2956_);
                if v___x_2957_ == 0 {
                    crate::leanh::lean_dec(v_j_2955_);
                    v___x_2958_ = crate::leanh::lean_box(0);
                    return v___x_2958_;
                } else {
                    v___x_2959_ = lean_array_fget_borrowed(v_as_2954_, v_j_2955_);
                    v___x_2960_ = lean_name_eq(v___x_2959_, v_declName_2953_);
                    if v___x_2960_ == 0 {
                        v___x_2961_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2962_ = lean_nat_add(v_j_2955_, v___x_2961_);
                        crate::leanh::lean_dec(v_j_2955_);
                        v_j_2955_ = v___x_2962_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2964_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2964_, 0, v_j_2955_);
                        return v___x_2964_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_findIdx_x3f_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2___boxed(
    mut v_declName_2965_: *mut crate::leanh::LeanObject,
    mut v_as_2966_: *mut crate::leanh::LeanObject,
    mut v_j_2967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2968_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2(v_declName_2965_, v_as_2966_, v_j_2967_);
    crate::leanh::lean_dec_ref(v_as_2966_);
    crate::leanh::lean_dec(v_declName_2965_);
    return v_res_2968_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0(
    mut v___y_2969_: *mut crate::leanh::LeanObject,
    mut v___y_2970_: *mut crate::leanh::LeanObject,
    mut v___y_2971_: *mut crate::leanh::LeanObject,
    mut v___y_2972_: *mut crate::leanh::LeanObject,
    mut v___y_2973_: *mut crate::leanh::LeanObject,
    mut v___y_2974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: u8 = 0;
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_2976_ = crate::leanh::lean_ctor_get(v___y_2973_, 5);
    v___x_2977_ = 0;
    v___x_2978_ = l_Lean_SourceInfo_fromRef(v_ref_2976_, v___x_2977_);
    v___x_2979_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2979_, 0, v___x_2978_);
    return v___x_2979_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0___boxed(
    mut v___y_2980_: *mut crate::leanh::LeanObject,
    mut v___y_2981_: *mut crate::leanh::LeanObject,
    mut v___y_2982_: *mut crate::leanh::LeanObject,
    mut v___y_2983_: *mut crate::leanh::LeanObject,
    mut v___y_2984_: *mut crate::leanh::LeanObject,
    mut v___y_2985_: *mut crate::leanh::LeanObject,
    mut v___y_2986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2987_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0(v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
    crate::leanh::lean_dec(v___y_2985_);
    crate::leanh::lean_dec_ref(v___y_2984_);
    crate::leanh::lean_dec(v___y_2983_);
    crate::leanh::lean_dec_ref(v___y_2982_);
    crate::leanh::lean_dec(v___y_2981_);
    crate::leanh::lean_dec_ref(v___y_2980_);
    return v_res_2987_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2998_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__4;
    v___x_2999_ = l_String_toRawSubstring_x27(v___x_2998_);
    return v___x_2999_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3028_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__18;
    v___x_3029_ = l_String_toRawSubstring_x27(v___x_3028_);
    return v___x_3029_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3071_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__36;
    v___x_3072_ = l_String_toRawSubstring_x27(v___x_3071_);
    return v___x_3072_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(
    mut v_upperBound_3085_: *mut crate::leanh::LeanObject,
    mut v___x_3086_: *mut crate::leanh::LeanObject,
    mut v_xs_3087_: *mut crate::leanh::LeanObject,
    mut v_allIndVals_3088_: *mut crate::leanh::LeanObject,
    mut v_ctx_3089_: *mut crate::leanh::LeanObject,
    mut v_a_3090_: *mut crate::leanh::LeanObject,
    mut v_b_3091_: *mut crate::leanh::LeanObject,
    mut v___y_3092_: *mut crate::leanh::LeanObject,
    mut v___y_3093_: *mut crate::leanh::LeanObject,
    mut v___y_3094_: *mut crate::leanh::LeanObject,
    mut v___y_3095_: *mut crate::leanh::LeanObject,
    mut v___y_3096_: *mut crate::leanh::LeanObject,
    mut v___y_3097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: u8 = 0;
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3120_: u8 = 0;
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3168_: u8 = 0;
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3172_: u8 = 0;
    let mut v_val_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxFunNames_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3213_: u8 = 0;
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3217_: u8 = 0;
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3259_: u8 = 0;
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3263_: u8 = 0;
    let mut v_isSharedCheck_3264_: u8 = 0;
    let mut v_a_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3268_: u8 = 0;
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3272_: u8 = 0;
    let mut v_a_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3276_: u8 = 0;
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3280_: u8 = 0;
    let mut v_a_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3284_: u8 = 0;
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3104_ = lean_nat_dec_lt(v_a_3090_, v_upperBound_3085_);
                if v___x_3104_ == 0 {
                    crate::leanh::lean_dec(v_a_3090_);
                    v___x_3105_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3105_, 0, v_b_3091_);
                    return v___x_3105_;
                } else {
                    v___x_3106_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__1;
                    v___x_3107_ =
                        l_Lean_Core_mkFreshUserName(v___x_3106_, v___y_3096_, v___y_3097_);
                    if crate::leanh::lean_obj_tag(v___x_3107_) == 0 {
                        v_a_3108_ = crate::leanh::lean_ctor_get(v___x_3107_, 0);
                        crate::leanh::lean_inc(v_a_3108_);
                        crate::leanh::lean_dec_ref_known(v___x_3107_, 1);
                        v___x_3109_ = l_Lean_instInhabitedExpr;
                        v___x_3110_ = lean_nat_add(v___x_3086_, v_a_3090_);
                        v___x_3111_ = lean_array_get_borrowed(v___x_3109_, v_xs_3087_, v___x_3110_);
                        crate::leanh::lean_dec(v___x_3110_);
                        crate::leanh::lean_inc(v___y_3097_);
                        crate::leanh::lean_inc_ref(v___y_3096_);
                        crate::leanh::lean_inc(v___y_3095_);
                        crate::leanh::lean_inc_ref(v___y_3094_);
                        crate::leanh::lean_inc(v___x_3111_);
                        v___x_3112_ = lean_infer_type(
                            v___x_3111_,
                            v___y_3094_,
                            v___y_3095_,
                            v___y_3096_,
                            v___y_3097_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3112_) == 0 {
                            v_a_3113_ = crate::leanh::lean_ctor_get(v___x_3112_, 0);
                            crate::leanh::lean_inc(v_a_3113_);
                            crate::leanh::lean_dec_ref_known(v___x_3112_, 1);
                            crate::leanh::lean_inc(v___y_3097_);
                            crate::leanh::lean_inc_ref(v___y_3096_);
                            crate::leanh::lean_inc(v___y_3095_);
                            crate::leanh::lean_inc_ref(v___y_3094_);
                            v___x_3114_ = lean_whnf(
                                v_a_3113_,
                                v___y_3094_,
                                v___y_3095_,
                                v___y_3096_,
                                v___y_3097_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3114_) == 0 {
                                v_a_3115_ = crate::leanh::lean_ctor_get(v___x_3114_, 0);
                                crate::leanh::lean_inc(v_a_3115_);
                                crate::leanh::lean_dec_ref_known(v___x_3114_, 1);
                                v_fst_3116_ = crate::leanh::lean_ctor_get(v_b_3091_, 0);
                                v_snd_3117_ = crate::leanh::lean_ctor_get(v_b_3091_, 1);
                                v_isSharedCheck_3264_ =
                                    (!crate::leanh::lean_is_exclusive(v_b_3091_)) as u8;
                                if v_isSharedCheck_3264_ == 0 {
                                    v___x_3119_ = v_b_3091_;
                                    v_isShared_3120_ = v_isSharedCheck_3264_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_snd_3117_);
                                    crate::leanh::lean_inc(v_fst_3116_);
                                    crate::leanh::lean_dec(v_b_3091_);
                                    v___x_3119_ = crate::leanh::lean_box(0);
                                    v_isShared_3120_ = v_isSharedCheck_3264_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3108_);
                                crate::leanh::lean_dec_ref(v_b_3091_);
                                crate::leanh::lean_dec(v_a_3090_);
                                v_a_3265_ = crate::leanh::lean_ctor_get(v___x_3114_, 0);
                                v_isSharedCheck_3272_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3114_)) as u8;
                                if v_isSharedCheck_3272_ == 0 {
                                    v___x_3267_ = v___x_3114_;
                                    v_isShared_3268_ = v_isSharedCheck_3272_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3265_);
                                    crate::leanh::lean_dec(v___x_3114_);
                                    v___x_3267_ = crate::leanh::lean_box(0);
                                    v_isShared_3268_ = v_isSharedCheck_3272_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3108_);
                            crate::leanh::lean_dec_ref(v_b_3091_);
                            crate::leanh::lean_dec(v_a_3090_);
                            v_a_3273_ = crate::leanh::lean_ctor_get(v___x_3112_, 0);
                            v_isSharedCheck_3280_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3112_)) as u8;
                            if v_isSharedCheck_3280_ == 0 {
                                v___x_3275_ = v___x_3112_;
                                v_isShared_3276_ = v_isSharedCheck_3280_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3273_);
                                crate::leanh::lean_dec(v___x_3112_);
                                v___x_3275_ = crate::leanh::lean_box(0);
                                v_isShared_3276_ = v_isSharedCheck_3280_;
                                state = 14;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_3091_);
                        crate::leanh::lean_dec(v_a_3090_);
                        v_a_3281_ = crate::leanh::lean_ctor_get(v___x_3107_, 0);
                        v_isSharedCheck_3288_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3107_)) as u8;
                        if v_isSharedCheck_3288_ == 0 {
                            v___x_3283_ = v___x_3107_;
                            v_isShared_3284_ = v_isSharedCheck_3288_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3281_);
                            crate::leanh::lean_dec(v___x_3107_);
                            v___x_3283_ = crate::leanh::lean_box(0);
                            v_isShared_3284_ = v_isSharedCheck_3288_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3101_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3102_ = lean_nat_add(v_a_3090_, v___x_3101_);
                crate::leanh::lean_dec(v_a_3090_);
                v_a_3090_ = v___x_3102_;
                v_b_3091_ = v_a_3100_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3121_ = lean_mk_syntax_ident(v_a_3108_);
                crate::leanh::lean_inc(v___x_3121_);
                v___x_3122_ = lean_array_push(v_fst_3116_, v___x_3121_);
                v___x_3123_ = l_Lean_Expr_getAppFn(v_a_3115_);
                crate::leanh::lean_dec(v_a_3115_);
                if crate::leanh::lean_obj_tag(v___x_3123_) == 4 {
                    v_declName_3124_ = crate::leanh::lean_ctor_get(v___x_3123_, 0);
                    crate::leanh::lean_inc(v_declName_3124_);
                    crate::leanh::lean_dec_ref_known(v___x_3123_, 2);
                    v___x_3125_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3126_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__2(v_declName_3124_, v_allIndVals_3088_, v___x_3125_);
                    crate::leanh::lean_dec(v_declName_3124_);
                    if crate::leanh::lean_obj_tag(v___x_3126_) == 0 {
                        v___x_3127_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0(v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
                        if crate::leanh::lean_obj_tag(v___x_3127_) == 0 {
                            v_a_3128_ = crate::leanh::lean_ctor_get(v___x_3127_, 0);
                            crate::leanh::lean_inc_n(v_a_3128_, 12);
                            crate::leanh::lean_dec_ref_known(v___x_3127_, 1);
                            v_quotContext_3129_ = crate::leanh::lean_ctor_get(v___y_3096_, 10);
                            v_currMacroScope_3130_ = crate::leanh::lean_ctor_get(v___y_3096_, 11);
                            v___x_3131_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3;
                            v___x_3132_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5);
                            v___x_3133_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__6;
                            crate::leanh::lean_inc_n(v_currMacroScope_3130_, 3);
                            crate::leanh::lean_inc_n(v_quotContext_3129_, 3);
                            v___x_3134_ = l_Lean_addMacroScope(
                                v_quotContext_3129_,
                                v___x_3133_,
                                v_currMacroScope_3130_,
                            );
                            v___x_3135_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__8;
                            v___x_3136_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3136_, 0, v_a_3128_);
                            crate::leanh::lean_ctor_set(v___x_3136_, 1, v___x_3132_);
                            crate::leanh::lean_ctor_set(v___x_3136_, 2, v___x_3134_);
                            crate::leanh::lean_ctor_set(v___x_3136_, 3, v___x_3135_);
                            v___x_3137_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10;
                            v___x_3138_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12;
                            v___x_3139_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14;
                            v___x_3140_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__15;
                            v___x_3141_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3141_, 0, v_a_3128_);
                            crate::leanh::lean_ctor_set(v___x_3141_, 1, v___x_3140_);
                            v___x_3142_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__17;
                            v___x_3143_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19);
                            v___x_3144_ = crate::leanh::lean_box(0);
                            v___x_3145_ = l_Lean_addMacroScope(
                                v_quotContext_3129_,
                                v___x_3144_,
                                v_currMacroScope_3130_,
                            );
                            v___x_3146_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__35;
                            v___x_3147_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3147_, 0, v_a_3128_);
                            crate::leanh::lean_ctor_set(v___x_3147_, 1, v___x_3143_);
                            crate::leanh::lean_ctor_set(v___x_3147_, 2, v___x_3145_);
                            crate::leanh::lean_ctor_set(v___x_3147_, 3, v___x_3146_);
                            v___x_3148_ = l_Lean_Syntax_node1(v_a_3128_, v___x_3142_, v___x_3147_);
                            v___x_3149_ = l_Lean_Syntax_node2(
                                v_a_3128_,
                                v___x_3139_,
                                v___x_3141_,
                                v___x_3148_,
                            );
                            v___x_3150_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37);
                            v___x_3151_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__38;
                            v___x_3152_ = l_Lean_addMacroScope(
                                v_quotContext_3129_,
                                v___x_3151_,
                                v_currMacroScope_3130_,
                            );
                            v___x_3153_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__41;
                            v___x_3154_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3154_, 0, v_a_3128_);
                            crate::leanh::lean_ctor_set(v___x_3154_, 1, v___x_3150_);
                            crate::leanh::lean_ctor_set(v___x_3154_, 2, v___x_3152_);
                            crate::leanh::lean_ctor_set(v___x_3154_, 3, v___x_3153_);
                            v___x_3155_ = l_Lean_Syntax_node1(v_a_3128_, v___x_3137_, v___x_3121_);
                            v___x_3156_ = l_Lean_Syntax_node2(
                                v_a_3128_,
                                v___x_3131_,
                                v___x_3154_,
                                v___x_3155_,
                            );
                            v___x_3157_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__42;
                            v___x_3158_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3158_, 0, v_a_3128_);
                            crate::leanh::lean_ctor_set(v___x_3158_, 1, v___x_3157_);
                            v___x_3159_ = l_Lean_Syntax_node3(
                                v_a_3128_,
                                v___x_3138_,
                                v___x_3149_,
                                v___x_3156_,
                                v___x_3158_,
                            );
                            v___x_3160_ = l_Lean_Syntax_node2(
                                v_a_3128_,
                                v___x_3137_,
                                v_snd_3117_,
                                v___x_3159_,
                            );
                            v___x_3161_ = l_Lean_Syntax_node2(
                                v_a_3128_,
                                v___x_3131_,
                                v___x_3136_,
                                v___x_3160_,
                            );
                            if v_isShared_3120_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3119_, 1, v___x_3161_);
                                crate::leanh::lean_ctor_set(v___x_3119_, 0, v___x_3122_);
                                v___x_3163_ = v___x_3119_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3164_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3122_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3164_, 1, v___x_3161_);
                                v___x_3163_ = v_reuseFailAlloc_3164_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_3122_);
                            crate::leanh::lean_dec(v___x_3121_);
                            crate::leanh::lean_del_object(v___x_3119_);
                            crate::leanh::lean_dec(v_snd_3117_);
                            crate::leanh::lean_dec(v_a_3090_);
                            v_a_3165_ = crate::leanh::lean_ctor_get(v___x_3127_, 0);
                            v_isSharedCheck_3172_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3127_)) as u8;
                            if v_isSharedCheck_3172_ == 0 {
                                v___x_3167_ = v___x_3127_;
                                v_isShared_3168_ = v_isSharedCheck_3172_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3165_);
                                crate::leanh::lean_dec(v___x_3127_);
                                v___x_3167_ = crate::leanh::lean_box(0);
                                v_isShared_3168_ = v_isSharedCheck_3172_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_val_3173_ = crate::leanh::lean_ctor_get(v___x_3126_, 0);
                        crate::leanh::lean_inc(v_val_3173_);
                        crate::leanh::lean_dec_ref_known(v___x_3126_, 1);
                        v___x_3174_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0(v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
                        if crate::leanh::lean_obj_tag(v___x_3174_) == 0 {
                            v_a_3175_ = crate::leanh::lean_ctor_get(v___x_3174_, 0);
                            crate::leanh::lean_inc_n(v_a_3175_, 11);
                            crate::leanh::lean_dec_ref_known(v___x_3174_, 1);
                            v_quotContext_3176_ = crate::leanh::lean_ctor_get(v___y_3096_, 10);
                            v_currMacroScope_3177_ = crate::leanh::lean_ctor_get(v___y_3096_, 11);
                            v___x_3178_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3;
                            v___x_3179_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5);
                            v___x_3180_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__6;
                            crate::leanh::lean_inc_n(v_currMacroScope_3177_, 2);
                            crate::leanh::lean_inc_n(v_quotContext_3176_, 2);
                            v___x_3181_ = l_Lean_addMacroScope(
                                v_quotContext_3176_,
                                v___x_3180_,
                                v_currMacroScope_3177_,
                            );
                            v___x_3182_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__8;
                            v___x_3183_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3183_, 0, v_a_3175_);
                            crate::leanh::lean_ctor_set(v___x_3183_, 1, v___x_3179_);
                            crate::leanh::lean_ctor_set(v___x_3183_, 2, v___x_3181_);
                            crate::leanh::lean_ctor_set(v___x_3183_, 3, v___x_3182_);
                            v___x_3184_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12;
                            v___x_3185_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14;
                            v___x_3186_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__15;
                            v___x_3187_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3187_, 0, v_a_3175_);
                            crate::leanh::lean_ctor_set(v___x_3187_, 1, v___x_3186_);
                            v___x_3188_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19);
                            v___x_3189_ = crate::leanh::lean_box(0);
                            v___x_3190_ = l_Lean_addMacroScope(
                                v_quotContext_3176_,
                                v___x_3189_,
                                v_currMacroScope_3177_,
                            );
                            v___x_3191_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__35;
                            v___x_3192_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3192_, 0, v_a_3175_);
                            crate::leanh::lean_ctor_set(v___x_3192_, 1, v___x_3188_);
                            crate::leanh::lean_ctor_set(v___x_3192_, 2, v___x_3190_);
                            crate::leanh::lean_ctor_set(v___x_3192_, 3, v___x_3191_);
                            v_auxFunNames_3193_ = crate::leanh::lean_ctor_get(v_ctx_3089_, 2);
                            v___x_3194_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__17;
                            v___x_3195_ = l_Lean_Syntax_node1(v_a_3175_, v___x_3194_, v___x_3192_);
                            v___x_3196_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10;
                            v___x_3197_ = l_Lean_Syntax_node2(
                                v_a_3175_,
                                v___x_3185_,
                                v___x_3187_,
                                v___x_3195_,
                            );
                            v___x_3198_ = lean_array_get_borrowed(
                                v___x_3189_,
                                v_auxFunNames_3193_,
                                v_val_3173_,
                            );
                            crate::leanh::lean_dec(v_val_3173_);
                            crate::leanh::lean_inc(v___x_3198_);
                            v___x_3199_ = lean_mk_syntax_ident(v___x_3198_);
                            v___x_3200_ = l_Lean_Syntax_node1(v_a_3175_, v___x_3196_, v___x_3121_);
                            v___x_3201_ = l_Lean_Syntax_node2(
                                v_a_3175_,
                                v___x_3178_,
                                v___x_3199_,
                                v___x_3200_,
                            );
                            v___x_3202_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__42;
                            v___x_3203_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3203_, 0, v_a_3175_);
                            crate::leanh::lean_ctor_set(v___x_3203_, 1, v___x_3202_);
                            v___x_3204_ = l_Lean_Syntax_node3(
                                v_a_3175_,
                                v___x_3184_,
                                v___x_3197_,
                                v___x_3201_,
                                v___x_3203_,
                            );
                            v___x_3205_ = l_Lean_Syntax_node2(
                                v_a_3175_,
                                v___x_3196_,
                                v_snd_3117_,
                                v___x_3204_,
                            );
                            v___x_3206_ = l_Lean_Syntax_node2(
                                v_a_3175_,
                                v___x_3178_,
                                v___x_3183_,
                                v___x_3205_,
                            );
                            if v_isShared_3120_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3119_, 1, v___x_3206_);
                                crate::leanh::lean_ctor_set(v___x_3119_, 0, v___x_3122_);
                                v___x_3208_ = v___x_3119_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_3209_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3122_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3209_, 1, v___x_3206_);
                                v___x_3208_ = v_reuseFailAlloc_3209_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_3173_);
                            crate::leanh::lean_dec_ref(v___x_3122_);
                            crate::leanh::lean_dec(v___x_3121_);
                            crate::leanh::lean_del_object(v___x_3119_);
                            crate::leanh::lean_dec(v_snd_3117_);
                            crate::leanh::lean_dec(v_a_3090_);
                            v_a_3210_ = crate::leanh::lean_ctor_get(v___x_3174_, 0);
                            v_isSharedCheck_3217_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3174_)) as u8;
                            if v_isSharedCheck_3217_ == 0 {
                                v___x_3212_ = v___x_3174_;
                                v_isShared_3213_ = v_isSharedCheck_3217_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3210_);
                                crate::leanh::lean_dec(v___x_3174_);
                                v___x_3212_ = crate::leanh::lean_box(0);
                                v_isShared_3213_ = v_isSharedCheck_3217_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3123_);
                    v___x_3218_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___lam__0(v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
                    if crate::leanh::lean_obj_tag(v___x_3218_) == 0 {
                        v_a_3219_ = crate::leanh::lean_ctor_get(v___x_3218_, 0);
                        crate::leanh::lean_inc_n(v_a_3219_, 12);
                        crate::leanh::lean_dec_ref_known(v___x_3218_, 1);
                        v_quotContext_3220_ = crate::leanh::lean_ctor_get(v___y_3096_, 10);
                        v_currMacroScope_3221_ = crate::leanh::lean_ctor_get(v___y_3096_, 11);
                        v___x_3222_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3;
                        v___x_3223_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__5);
                        v___x_3224_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__6;
                        crate::leanh::lean_inc_n(v_currMacroScope_3221_, 3);
                        crate::leanh::lean_inc_n(v_quotContext_3220_, 3);
                        v___x_3225_ = l_Lean_addMacroScope(
                            v_quotContext_3220_,
                            v___x_3224_,
                            v_currMacroScope_3221_,
                        );
                        v___x_3226_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__8;
                        v___x_3227_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3227_, 0, v_a_3219_);
                        crate::leanh::lean_ctor_set(v___x_3227_, 1, v___x_3223_);
                        crate::leanh::lean_ctor_set(v___x_3227_, 2, v___x_3225_);
                        crate::leanh::lean_ctor_set(v___x_3227_, 3, v___x_3226_);
                        v___x_3228_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10;
                        v___x_3229_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__12;
                        v___x_3230_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__14;
                        v___x_3231_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__15;
                        v___x_3232_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3232_, 0, v_a_3219_);
                        crate::leanh::lean_ctor_set(v___x_3232_, 1, v___x_3231_);
                        v___x_3233_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__17;
                        v___x_3234_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__19);
                        v___x_3235_ = crate::leanh::lean_box(0);
                        v___x_3236_ = l_Lean_addMacroScope(
                            v_quotContext_3220_,
                            v___x_3235_,
                            v_currMacroScope_3221_,
                        );
                        v___x_3237_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__35;
                        v___x_3238_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3238_, 0, v_a_3219_);
                        crate::leanh::lean_ctor_set(v___x_3238_, 1, v___x_3234_);
                        crate::leanh::lean_ctor_set(v___x_3238_, 2, v___x_3236_);
                        crate::leanh::lean_ctor_set(v___x_3238_, 3, v___x_3237_);
                        v___x_3239_ = l_Lean_Syntax_node1(v_a_3219_, v___x_3233_, v___x_3238_);
                        v___x_3240_ =
                            l_Lean_Syntax_node2(v_a_3219_, v___x_3230_, v___x_3232_, v___x_3239_);
                        v___x_3241_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__37);
                        v___x_3242_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__38;
                        v___x_3243_ = l_Lean_addMacroScope(
                            v_quotContext_3220_,
                            v___x_3242_,
                            v_currMacroScope_3221_,
                        );
                        v___x_3244_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__41;
                        v___x_3245_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3245_, 0, v_a_3219_);
                        crate::leanh::lean_ctor_set(v___x_3245_, 1, v___x_3241_);
                        crate::leanh::lean_ctor_set(v___x_3245_, 2, v___x_3243_);
                        crate::leanh::lean_ctor_set(v___x_3245_, 3, v___x_3244_);
                        v___x_3246_ = l_Lean_Syntax_node1(v_a_3219_, v___x_3228_, v___x_3121_);
                        v___x_3247_ =
                            l_Lean_Syntax_node2(v_a_3219_, v___x_3222_, v___x_3245_, v___x_3246_);
                        v___x_3248_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__42;
                        v___x_3249_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3249_, 0, v_a_3219_);
                        crate::leanh::lean_ctor_set(v___x_3249_, 1, v___x_3248_);
                        v___x_3250_ = l_Lean_Syntax_node3(
                            v_a_3219_,
                            v___x_3229_,
                            v___x_3240_,
                            v___x_3247_,
                            v___x_3249_,
                        );
                        v___x_3251_ =
                            l_Lean_Syntax_node2(v_a_3219_, v___x_3228_, v_snd_3117_, v___x_3250_);
                        v___x_3252_ =
                            l_Lean_Syntax_node2(v_a_3219_, v___x_3222_, v___x_3227_, v___x_3251_);
                        if v_isShared_3120_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3119_, 1, v___x_3252_);
                            crate::leanh::lean_ctor_set(v___x_3119_, 0, v___x_3122_);
                            v___x_3254_ = v___x_3119_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_3255_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3122_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3255_, 1, v___x_3252_);
                            v___x_3254_ = v_reuseFailAlloc_3255_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3122_);
                        crate::leanh::lean_dec(v___x_3121_);
                        crate::leanh::lean_del_object(v___x_3119_);
                        crate::leanh::lean_dec(v_snd_3117_);
                        crate::leanh::lean_dec(v_a_3090_);
                        v_a_3256_ = crate::leanh::lean_ctor_get(v___x_3218_, 0);
                        v_isSharedCheck_3263_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3218_)) as u8;
                        if v_isSharedCheck_3263_ == 0 {
                            v___x_3258_ = v___x_3218_;
                            v_isShared_3259_ = v_isSharedCheck_3263_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3256_);
                            crate::leanh::lean_dec(v___x_3218_);
                            v___x_3258_ = crate::leanh::lean_box(0);
                            v_isShared_3259_ = v_isSharedCheck_3263_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v_a_3100_ = v___x_3163_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_3168_ == 0 {
                    v___x_3170_ = v___x_3167_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3171_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
                    v___x_3170_ = v_reuseFailAlloc_3171_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3170_;
            }
            6 => {
                v_a_3100_ = v___x_3208_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_3213_ == 0 {
                    v___x_3215_ = v___x_3212_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3216_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
                    v___x_3215_ = v_reuseFailAlloc_3216_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3215_;
            }
            9 => {
                v_a_3100_ = v___x_3254_;
                state = 1;
                continue;
            }
            10 => {
                if v_isShared_3259_ == 0 {
                    v___x_3261_ = v___x_3258_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3262_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
                    v___x_3261_ = v_reuseFailAlloc_3262_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3261_;
            }
            12 => {
                if v_isShared_3268_ == 0 {
                    v___x_3270_ = v___x_3267_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3271_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3265_);
                    v___x_3270_ = v_reuseFailAlloc_3271_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3270_;
            }
            14 => {
                if v_isShared_3276_ == 0 {
                    v___x_3278_ = v___x_3275_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3279_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
                    v___x_3278_ = v_reuseFailAlloc_3279_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3278_;
            }
            16 => {
                if v_isShared_3284_ == 0 {
                    v___x_3286_ = v___x_3283_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3287_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
                    v___x_3286_ = v_reuseFailAlloc_3287_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3286_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___boxed(
    mut v_upperBound_3289_: *mut crate::leanh::LeanObject,
    mut v___x_3290_: *mut crate::leanh::LeanObject,
    mut v_xs_3291_: *mut crate::leanh::LeanObject,
    mut v_allIndVals_3292_: *mut crate::leanh::LeanObject,
    mut v_ctx_3293_: *mut crate::leanh::LeanObject,
    mut v_a_3294_: *mut crate::leanh::LeanObject,
    mut v_b_3295_: *mut crate::leanh::LeanObject,
    mut v___y_3296_: *mut crate::leanh::LeanObject,
    mut v___y_3297_: *mut crate::leanh::LeanObject,
    mut v___y_3298_: *mut crate::leanh::LeanObject,
    mut v___y_3299_: *mut crate::leanh::LeanObject,
    mut v___y_3300_: *mut crate::leanh::LeanObject,
    mut v___y_3301_: *mut crate::leanh::LeanObject,
    mut v___y_3302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3303_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(v_upperBound_3289_, v___x_3290_, v_xs_3291_, v_allIndVals_3292_, v_ctx_3293_, v_a_3294_, v_b_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
    crate::leanh::lean_dec(v___y_3301_);
    crate::leanh::lean_dec_ref(v___y_3300_);
    crate::leanh::lean_dec(v___y_3299_);
    crate::leanh::lean_dec_ref(v___y_3298_);
    crate::leanh::lean_dec(v___y_3297_);
    crate::leanh::lean_dec_ref(v___y_3296_);
    crate::leanh::lean_dec_ref(v_ctx_3293_);
    crate::leanh::lean_dec_ref(v_allIndVals_3292_);
    crate::leanh::lean_dec_ref(v_xs_3291_);
    crate::leanh::lean_dec(v___x_3290_);
    crate::leanh::lean_dec(v_upperBound_3289_);
    return v_res_3303_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3311_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_3311_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3320_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__7;
    v___x_3321_ = l_Lean_mkAtom(v___x_3320_);
    return v___x_3321_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1(
    mut v_indVal_3323_: *mut crate::leanh::LeanObject,
    mut v___x_3324_: *mut crate::leanh::LeanObject,
    mut v_alts_3325_: *mut crate::leanh::LeanObject,
    mut v_snd_3326_: *mut crate::leanh::LeanObject,
    mut v_numFields_3327_: *mut crate::leanh::LeanObject,
    mut v_allIndVals_3328_: *mut crate::leanh::LeanObject,
    mut v_ctx_3329_: *mut crate::leanh::LeanObject,
    mut v___f_3330_: *mut crate::leanh::LeanObject,
    mut v_head_3331_: *mut crate::leanh::LeanObject,
    mut v_xs_3332_: *mut crate::leanh::LeanObject,
    mut v_x_3333_: *mut crate::leanh::LeanObject,
    mut v___y_3334_: *mut crate::leanh::LeanObject,
    mut v___y_3335_: *mut crate::leanh::LeanObject,
    mut v___y_3336_: *mut crate::leanh::LeanObject,
    mut v___y_3337_: *mut crate::leanh::LeanObject,
    mut v___y_3338_: *mut crate::leanh::LeanObject,
    mut v___y_3339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numParams_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3359_: u8 = 0;
    let mut v_fst_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3364_: u8 = 0;
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3381_: usize = 0;
    let mut v___x_3382_: usize = 0;
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3396_: u8 = 0;
    let mut v_isSharedCheck_3397_: u8 = 0;
    let mut v_a_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3401_: u8 = 0;
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3405_: u8 = 0;
    let mut v_a_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3409_: u8 = 0;
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3413_: u8 = 0;
    let mut v_a_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3417_: u8 = 0;
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3421_: u8 = 0;
    let mut v_a_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3425_: u8 = 0;
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3429_: u8 = 0;
    let mut v_a_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3433_: u8 = 0;
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3437_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_numParams_3341_ = crate::leanh::lean_ctor_get(v_indVal_3323_, 1);
                v_numIndices_3342_ = crate::leanh::lean_ctor_get(v_indVal_3323_, 2);
                crate::leanh::lean_inc_ref(v_alts_3325_);
                crate::leanh::lean_inc(v___x_3324_);
                v___x_3343_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(v_numIndices_3342_, v___x_3324_, v_alts_3325_, v___y_3338_);
                if crate::leanh::lean_obj_tag(v___x_3343_) == 0 {
                    v_a_3344_ = crate::leanh::lean_ctor_get(v___x_3343_, 0);
                    crate::leanh::lean_inc(v_a_3344_);
                    crate::leanh::lean_dec_ref_known(v___x_3343_, 1);
                    crate::leanh::lean_inc(v___x_3324_);
                    v___x_3345_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(v_numParams_3341_, v___x_3324_, v_alts_3325_, v___y_3338_);
                    if crate::leanh::lean_obj_tag(v___x_3345_) == 0 {
                        v_a_3346_ = crate::leanh::lean_ctor_get(v___x_3345_, 0);
                        crate::leanh::lean_inc(v_a_3346_);
                        crate::leanh::lean_dec_ref_known(v___x_3345_, 1);
                        v___x_3347_ = l_Nat_reprFast(v_snd_3326_);
                        v___x_3348_ = crate::leanh::lean_box(2);
                        v___x_3349_ = l_Lean_Syntax_mkNumLit(v___x_3347_, v___x_3348_);
                        v___x_3350_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3350_, 0, v_a_3346_);
                        crate::leanh::lean_ctor_set(v___x_3350_, 1, v___x_3349_);
                        v___x_3351_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(v_numFields_3327_, v_numParams_3341_, v_xs_3332_, v_allIndVals_3328_, v_ctx_3329_, v___x_3324_, v___x_3350_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
                        if crate::leanh::lean_obj_tag(v___x_3351_) == 0 {
                            v_a_3352_ = crate::leanh::lean_ctor_get(v___x_3351_, 0);
                            crate::leanh::lean_inc(v_a_3352_);
                            crate::leanh::lean_dec_ref_known(v___x_3351_, 1);
                            crate::leanh::lean_inc_ref(v___f_3330_);
                            crate::leanh::lean_inc(v___y_3339_);
                            crate::leanh::lean_inc_ref(v___y_3338_);
                            crate::leanh::lean_inc(v___y_3337_);
                            crate::leanh::lean_inc_ref(v___y_3336_);
                            crate::leanh::lean_inc(v___y_3335_);
                            crate::leanh::lean_inc_ref(v___y_3334_);
                            v___x_3353_ = crate::leanh::lean_apply_7(
                                v___f_3330_,
                                v___y_3334_,
                                v___y_3335_,
                                v___y_3336_,
                                v___y_3337_,
                                v___y_3338_,
                                v___y_3339_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_3353_) == 0 {
                                v_a_3354_ = crate::leanh::lean_ctor_get(v___x_3353_, 0);
                                crate::leanh::lean_inc(v_a_3354_);
                                crate::leanh::lean_dec_ref_known(v___x_3353_, 1);
                                crate::leanh::lean_inc(v___y_3339_);
                                crate::leanh::lean_inc_ref(v___y_3338_);
                                crate::leanh::lean_inc(v___y_3337_);
                                crate::leanh::lean_inc_ref(v___y_3336_);
                                crate::leanh::lean_inc(v___y_3335_);
                                crate::leanh::lean_inc_ref(v___y_3334_);
                                v___x_3355_ = crate::leanh::lean_apply_7(
                                    v___f_3330_,
                                    v___y_3334_,
                                    v___y_3335_,
                                    v___y_3336_,
                                    v___y_3337_,
                                    v___y_3338_,
                                    v___y_3339_,
                                    crate::leanh::lean_box(0),
                                );
                                if crate::leanh::lean_obj_tag(v___x_3355_) == 0 {
                                    v_a_3356_ = crate::leanh::lean_ctor_get(v___x_3355_, 0);
                                    v_isSharedCheck_3397_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3355_)) as u8;
                                    if v_isSharedCheck_3397_ == 0 {
                                        v___x_3358_ = v___x_3355_;
                                        v_isShared_3359_ = v_isSharedCheck_3397_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3356_);
                                        crate::leanh::lean_dec(v___x_3355_);
                                        v___x_3358_ = crate::leanh::lean_box(0);
                                        v_isShared_3359_ = v_isSharedCheck_3397_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_3354_);
                                    crate::leanh::lean_dec(v_a_3352_);
                                    crate::leanh::lean_dec(v_a_3344_);
                                    crate::leanh::lean_dec(v_head_3331_);
                                    v_a_3398_ = crate::leanh::lean_ctor_get(v___x_3355_, 0);
                                    v_isSharedCheck_3405_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3355_)) as u8;
                                    if v_isSharedCheck_3405_ == 0 {
                                        v___x_3400_ = v___x_3355_;
                                        v_isShared_3401_ = v_isSharedCheck_3405_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3398_);
                                        crate::leanh::lean_dec(v___x_3355_);
                                        v___x_3400_ = crate::leanh::lean_box(0);
                                        v_isShared_3401_ = v_isSharedCheck_3405_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3352_);
                                crate::leanh::lean_dec(v_a_3344_);
                                crate::leanh::lean_dec(v_head_3331_);
                                crate::leanh::lean_dec_ref(v___f_3330_);
                                v_a_3406_ = crate::leanh::lean_ctor_get(v___x_3353_, 0);
                                v_isSharedCheck_3413_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3353_)) as u8;
                                if v_isSharedCheck_3413_ == 0 {
                                    v___x_3408_ = v___x_3353_;
                                    v_isShared_3409_ = v_isSharedCheck_3413_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3406_);
                                    crate::leanh::lean_dec(v___x_3353_);
                                    v___x_3408_ = crate::leanh::lean_box(0);
                                    v_isShared_3409_ = v_isSharedCheck_3413_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3344_);
                            crate::leanh::lean_dec(v_head_3331_);
                            crate::leanh::lean_dec_ref(v___f_3330_);
                            v_a_3414_ = crate::leanh::lean_ctor_get(v___x_3351_, 0);
                            v_isSharedCheck_3421_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3351_)) as u8;
                            if v_isSharedCheck_3421_ == 0 {
                                v___x_3416_ = v___x_3351_;
                                v_isShared_3417_ = v_isSharedCheck_3421_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3414_);
                                crate::leanh::lean_dec(v___x_3351_);
                                v___x_3416_ = crate::leanh::lean_box(0);
                                v_isShared_3417_ = v_isSharedCheck_3421_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3344_);
                        crate::leanh::lean_dec(v_head_3331_);
                        crate::leanh::lean_dec_ref(v___f_3330_);
                        crate::leanh::lean_dec(v_snd_3326_);
                        crate::leanh::lean_dec(v___x_3324_);
                        v_a_3422_ = crate::leanh::lean_ctor_get(v___x_3345_, 0);
                        v_isSharedCheck_3429_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3345_)) as u8;
                        if v_isSharedCheck_3429_ == 0 {
                            v___x_3424_ = v___x_3345_;
                            v_isShared_3425_ = v_isSharedCheck_3429_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3422_);
                            crate::leanh::lean_dec(v___x_3345_);
                            v___x_3424_ = crate::leanh::lean_box(0);
                            v_isShared_3425_ = v_isSharedCheck_3429_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_head_3331_);
                    crate::leanh::lean_dec_ref(v___f_3330_);
                    crate::leanh::lean_dec(v_snd_3326_);
                    crate::leanh::lean_dec_ref(v_alts_3325_);
                    crate::leanh::lean_dec(v___x_3324_);
                    v_a_3430_ = crate::leanh::lean_ctor_get(v___x_3343_, 0);
                    v_isSharedCheck_3437_ = (!crate::leanh::lean_is_exclusive(v___x_3343_)) as u8;
                    if v_isSharedCheck_3437_ == 0 {
                        v___x_3432_ = v___x_3343_;
                        v_isShared_3433_ = v_isSharedCheck_3437_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3430_);
                        crate::leanh::lean_dec(v___x_3343_);
                        v___x_3432_ = crate::leanh::lean_box(0);
                        v_isShared_3433_ = v_isSharedCheck_3437_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3360_ = crate::leanh::lean_ctor_get(v_a_3352_, 0);
                v_snd_3361_ = crate::leanh::lean_ctor_get(v_a_3352_, 1);
                v_isSharedCheck_3396_ = (!crate::leanh::lean_is_exclusive(v_a_3352_)) as u8;
                if v_isSharedCheck_3396_ == 0 {
                    v___x_3363_ = v_a_3352_;
                    v_isShared_3364_ = v_isSharedCheck_3396_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3361_);
                    crate::leanh::lean_inc(v_fst_3360_);
                    crate::leanh::lean_dec(v_a_3352_);
                    v___x_3363_ = crate::leanh::lean_box(0);
                    v_isShared_3364_ = v_isSharedCheck_3396_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3365_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__3;
                v___x_3366_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__0;
                crate::leanh::lean_inc(v_a_3354_);
                if v_isShared_3364_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3363_, 2);
                    crate::leanh::lean_ctor_set(v___x_3363_, 1, v___x_3366_);
                    crate::leanh::lean_ctor_set(v___x_3363_, 0, v_a_3354_);
                    v___x_3368_ = v___x_3363_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3395_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3354_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3395_, 1, v___x_3366_);
                    v___x_3368_ = v_reuseFailAlloc_3395_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3369_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__2;
                v___x_3370_ = lean_mk_syntax_ident(v_head_3331_);
                crate::leanh::lean_inc_n(v_a_3354_, 2);
                v___x_3371_ = l_Lean_Syntax_node2(v_a_3354_, v___x_3369_, v___x_3368_, v___x_3370_);
                v___x_3372_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10;
                v___x_3373_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3);
                v___x_3374_ = l_Array_append___redArg(v___x_3373_, v_fst_3360_);
                crate::leanh::lean_dec(v_fst_3360_);
                v___x_3375_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3375_, 0, v_a_3354_);
                crate::leanh::lean_ctor_set(v___x_3375_, 1, v___x_3372_);
                crate::leanh::lean_ctor_set(v___x_3375_, 2, v___x_3374_);
                v___x_3376_ = l_Lean_Syntax_node2(v_a_3354_, v___x_3365_, v___x_3371_, v___x_3375_);
                v___x_3377_ = lean_array_push(v_a_3344_, v___x_3376_);
                v___x_3378_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__5;
                v___x_3379_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__6;
                crate::leanh::lean_inc_n(v_a_3356_, 4);
                v___x_3380_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3380_, 0, v_a_3356_);
                crate::leanh::lean_ctor_set(v___x_3380_, 1, v___x_3379_);
                v_sz_3381_ = lean_array_size(v___x_3377_);
                v___x_3382_ = 0usize;
                v___x_3383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1(v_sz_3381_, v___x_3382_, v___x_3377_);
                v___x_3384_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8);
                v___x_3385_ = l_Lean_mkSepArray(v___x_3383_, v___x_3384_);
                crate::leanh::lean_dec_ref(v___x_3383_);
                v___x_3386_ = l_Array_append___redArg(v___x_3373_, v___x_3385_);
                crate::leanh::lean_dec_ref(v___x_3385_);
                v___x_3387_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3387_, 0, v_a_3356_);
                crate::leanh::lean_ctor_set(v___x_3387_, 1, v___x_3372_);
                crate::leanh::lean_ctor_set(v___x_3387_, 2, v___x_3386_);
                v___x_3388_ = l_Lean_Syntax_node1(v_a_3356_, v___x_3372_, v___x_3387_);
                v___x_3389_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__9;
                v___x_3390_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3390_, 0, v_a_3356_);
                crate::leanh::lean_ctor_set(v___x_3390_, 1, v___x_3389_);
                v___x_3391_ = l_Lean_Syntax_node4(
                    v_a_3356_,
                    v___x_3378_,
                    v___x_3380_,
                    v___x_3388_,
                    v___x_3390_,
                    v_snd_3361_,
                );
                if v_isShared_3359_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3358_, 0, v___x_3391_);
                    v___x_3393_ = v___x_3358_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3394_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3391_);
                    v___x_3393_ = v_reuseFailAlloc_3394_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3393_;
            }
            5 => {
                if v_isShared_3401_ == 0 {
                    v___x_3403_ = v___x_3400_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3404_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
                    v___x_3403_ = v_reuseFailAlloc_3404_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3403_;
            }
            7 => {
                if v_isShared_3409_ == 0 {
                    v___x_3411_ = v___x_3408_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3412_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
                    v___x_3411_ = v_reuseFailAlloc_3412_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3411_;
            }
            9 => {
                if v_isShared_3417_ == 0 {
                    v___x_3419_ = v___x_3416_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3420_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
                    v___x_3419_ = v_reuseFailAlloc_3420_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3419_;
            }
            11 => {
                if v_isShared_3425_ == 0 {
                    v___x_3427_ = v___x_3424_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3428_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
                    v___x_3427_ = v_reuseFailAlloc_3428_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3427_;
            }
            13 => {
                if v_isShared_3433_ == 0 {
                    v___x_3435_ = v___x_3432_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3436_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
                    v___x_3435_ = v_reuseFailAlloc_3436_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3435_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_indVal_3438_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_3439_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_alts_3440_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_snd_3441_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_numFields_3442_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_allIndVals_3443_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_ctx_3444_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___f_3445_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_head_3446_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_xs_3447_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_x_3448_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_3449_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_3450_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3451_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3452_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3453_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3454_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_3455_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3456_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1(v_indVal_3438_, v___x_3439_, v_alts_3440_, v_snd_3441_, v_numFields_3442_, v_allIndVals_3443_, v_ctx_3444_, v___f_3445_, v_head_3446_, v_xs_3447_, v_x_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
    crate::leanh::lean_dec(v___y_3454_);
    crate::leanh::lean_dec_ref(v___y_3453_);
    crate::leanh::lean_dec(v___y_3452_);
    crate::leanh::lean_dec_ref(v___y_3451_);
    crate::leanh::lean_dec(v___y_3450_);
    crate::leanh::lean_dec_ref(v___y_3449_);
    crate::leanh::lean_dec_ref(v_x_3448_);
    crate::leanh::lean_dec_ref(v_xs_3447_);
    crate::leanh::lean_dec_ref(v_ctx_3444_);
    crate::leanh::lean_dec_ref(v_allIndVals_3443_);
    crate::leanh::lean_dec(v_numFields_3442_);
    crate::leanh::lean_dec_ref(v_indVal_3438_);
    return v_res_3456_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__0(
    mut v___y_3457_: *mut crate::leanh::LeanObject,
    mut v___y_3458_: *mut crate::leanh::LeanObject,
    mut v___y_3459_: *mut crate::leanh::LeanObject,
    mut v___y_3460_: *mut crate::leanh::LeanObject,
    mut v___y_3461_: *mut crate::leanh::LeanObject,
    mut v___y_3462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: u8 = 0;
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_3464_ = crate::leanh::lean_ctor_get(v___y_3461_, 5);
    v___x_3465_ = 0;
    v___x_3466_ = l_Lean_SourceInfo_fromRef(v_ref_3464_, v___x_3465_);
    v___x_3467_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3467_, 0, v___x_3466_);
    return v___x_3467_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__0___boxed(
    mut v___y_3468_: *mut crate::leanh::LeanObject,
    mut v___y_3469_: *mut crate::leanh::LeanObject,
    mut v___y_3470_: *mut crate::leanh::LeanObject,
    mut v___y_3471_: *mut crate::leanh::LeanObject,
    mut v___y_3472_: *mut crate::leanh::LeanObject,
    mut v___y_3473_: *mut crate::leanh::LeanObject,
    mut v___y_3474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3475_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__0(v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
    crate::leanh::lean_dec(v___y_3473_);
    crate::leanh::lean_dec_ref(v___y_3472_);
    crate::leanh::lean_dec(v___y_3471_);
    crate::leanh::lean_dec_ref(v___y_3470_);
    crate::leanh::lean_dec(v___y_3469_);
    crate::leanh::lean_dec_ref(v___y_3468_);
    return v_res_3475_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg(
    mut v_indVal_3479_: *mut crate::leanh::LeanObject,
    mut v_allIndVals_3480_: *mut crate::leanh::LeanObject,
    mut v_ctx_3481_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3482_: *mut crate::leanh::LeanObject,
    mut v_b_3483_: *mut crate::leanh::LeanObject,
    mut v___y_3484_: *mut crate::leanh::LeanObject,
    mut v___y_3485_: *mut crate::leanh::LeanObject,
    mut v___y_3486_: *mut crate::leanh::LeanObject,
    mut v___y_3487_: *mut crate::leanh::LeanObject,
    mut v___y_3488_: *mut crate::leanh::LeanObject,
    mut v___y_3489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3501_: u8 = 0;
    let mut v_numFields_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: u8 = 0;
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3521_: u8 = 0;
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3525_: u8 = 0;
    let mut v_isSharedCheck_3526_: u8 = 0;
    let mut v_a_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3530_: u8 = 0;
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3534_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3482_) == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_3481_);
                    crate::leanh::lean_dec_ref(v_allIndVals_3480_);
                    crate::leanh::lean_dec_ref(v_indVal_3479_);
                    v___x_3491_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3491_, 0, v_b_3483_);
                    return v___x_3491_;
                } else {
                    v_head_3492_ = crate::leanh::lean_ctor_get(v_as_x27_3482_, 0);
                    v_tail_3493_ = crate::leanh::lean_ctor_get(v_as_x27_3482_, 1);
                    crate::leanh::lean_inc(v_head_3492_);
                    v___x_3494_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0(v_head_3492_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
                    if crate::leanh::lean_obj_tag(v___x_3494_) == 0 {
                        v_a_3495_ = crate::leanh::lean_ctor_get(v___x_3494_, 0);
                        crate::leanh::lean_inc(v_a_3495_);
                        crate::leanh::lean_dec_ref_known(v___x_3494_, 1);
                        v_toConstantVal_3496_ = crate::leanh::lean_ctor_get(v_a_3495_, 0);
                        crate::leanh::lean_inc_ref(v_toConstantVal_3496_);
                        v_fst_3497_ = crate::leanh::lean_ctor_get(v_b_3483_, 0);
                        v_snd_3498_ = crate::leanh::lean_ctor_get(v_b_3483_, 1);
                        v_isSharedCheck_3526_ = (!crate::leanh::lean_is_exclusive(v_b_3483_)) as u8;
                        if v_isSharedCheck_3526_ == 0 {
                            v___x_3500_ = v_b_3483_;
                            v_isShared_3501_ = v_isSharedCheck_3526_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3498_);
                            crate::leanh::lean_inc(v_fst_3497_);
                            crate::leanh::lean_dec(v_b_3483_);
                            v___x_3500_ = crate::leanh::lean_box(0);
                            v_isShared_3501_ = v_isSharedCheck_3526_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_3483_);
                        crate::leanh::lean_dec_ref(v_ctx_3481_);
                        crate::leanh::lean_dec_ref(v_allIndVals_3480_);
                        crate::leanh::lean_dec_ref(v_indVal_3479_);
                        v_a_3527_ = crate::leanh::lean_ctor_get(v___x_3494_, 0);
                        v_isSharedCheck_3534_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3494_)) as u8;
                        if v_isSharedCheck_3534_ == 0 {
                            v___x_3529_ = v___x_3494_;
                            v_isShared_3530_ = v_isSharedCheck_3534_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3527_);
                            crate::leanh::lean_dec(v___x_3494_);
                            v___x_3529_ = crate::leanh::lean_box(0);
                            v_isShared_3530_ = v_isSharedCheck_3534_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_numFields_3502_ = crate::leanh::lean_ctor_get(v_a_3495_, 4);
                crate::leanh::lean_inc(v_numFields_3502_);
                crate::leanh::lean_dec(v_a_3495_);
                v_type_3503_ = crate::leanh::lean_ctor_get(v_toConstantVal_3496_, 2);
                crate::leanh::lean_inc_ref(v_type_3503_);
                crate::leanh::lean_dec_ref(v_toConstantVal_3496_);
                v___f_3504_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__0;
                v___x_3505_ = crate::leanh::lean_unsigned_to_nat(0);
                v_alts_3506_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__1;
                crate::leanh::lean_inc(v_head_3492_);
                crate::leanh::lean_inc_ref(v_ctx_3481_);
                crate::leanh::lean_inc_ref(v_allIndVals_3480_);
                crate::leanh::lean_inc(v_snd_3498_);
                crate::leanh::lean_inc_ref(v_indVal_3479_);
                v___f_3507_ = crate::leanh::lean_alloc_closure(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___boxed as *mut core::ffi::c_void, 18, 9);
                crate::leanh::lean_closure_set(v___f_3507_, 0, v_indVal_3479_);
                crate::leanh::lean_closure_set(v___f_3507_, 1, v___x_3505_);
                crate::leanh::lean_closure_set(v___f_3507_, 2, v_alts_3506_);
                crate::leanh::lean_closure_set(v___f_3507_, 3, v_snd_3498_);
                crate::leanh::lean_closure_set(v___f_3507_, 4, v_numFields_3502_);
                crate::leanh::lean_closure_set(v___f_3507_, 5, v_allIndVals_3480_);
                crate::leanh::lean_closure_set(v___f_3507_, 6, v_ctx_3481_);
                crate::leanh::lean_closure_set(v___f_3507_, 7, v___f_3504_);
                crate::leanh::lean_closure_set(v___f_3507_, 8, v_head_3492_);
                v___x_3508_ = 0;
                v___x_3509_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__5___redArg(v_type_3503_, v___f_3507_, v___x_3508_, v___x_3508_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
                if crate::leanh::lean_obj_tag(v___x_3509_) == 0 {
                    v_a_3510_ = crate::leanh::lean_ctor_get(v___x_3509_, 0);
                    crate::leanh::lean_inc(v_a_3510_);
                    crate::leanh::lean_dec_ref_known(v___x_3509_, 1);
                    v___x_3511_ = lean_array_push(v_fst_3497_, v_a_3510_);
                    v___x_3512_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3513_ = lean_nat_add(v_snd_3498_, v___x_3512_);
                    crate::leanh::lean_dec(v_snd_3498_);
                    if v_isShared_3501_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3500_, 1, v___x_3513_);
                        crate::leanh::lean_ctor_set(v___x_3500_, 0, v___x_3511_);
                        v___x_3515_ = v___x_3500_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3517_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3511_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 1, v___x_3513_);
                        v___x_3515_ = v_reuseFailAlloc_3517_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3500_);
                    crate::leanh::lean_dec(v_snd_3498_);
                    crate::leanh::lean_dec(v_fst_3497_);
                    crate::leanh::lean_dec_ref(v_ctx_3481_);
                    crate::leanh::lean_dec_ref(v_allIndVals_3480_);
                    crate::leanh::lean_dec_ref(v_indVal_3479_);
                    v_a_3518_ = crate::leanh::lean_ctor_get(v___x_3509_, 0);
                    v_isSharedCheck_3525_ = (!crate::leanh::lean_is_exclusive(v___x_3509_)) as u8;
                    if v_isSharedCheck_3525_ == 0 {
                        v___x_3520_ = v___x_3509_;
                        v_isShared_3521_ = v_isSharedCheck_3525_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3518_);
                        crate::leanh::lean_dec(v___x_3509_);
                        v___x_3520_ = crate::leanh::lean_box(0);
                        v_isShared_3521_ = v_isSharedCheck_3525_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_as_x27_3482_ = v_tail_3493_;
                v_b_3483_ = v___x_3515_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_3521_ == 0 {
                    v___x_3523_ = v___x_3520_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3524_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
                    v___x_3523_ = v_reuseFailAlloc_3524_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3523_;
            }
            5 => {
                if v_isShared_3530_ == 0 {
                    v___x_3532_ = v___x_3529_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3533_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3527_);
                    v___x_3532_ = v_reuseFailAlloc_3533_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3532_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___boxed(
    mut v_indVal_3535_: *mut crate::leanh::LeanObject,
    mut v_allIndVals_3536_: *mut crate::leanh::LeanObject,
    mut v_ctx_3537_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3538_: *mut crate::leanh::LeanObject,
    mut v_b_3539_: *mut crate::leanh::LeanObject,
    mut v___y_3540_: *mut crate::leanh::LeanObject,
    mut v___y_3541_: *mut crate::leanh::LeanObject,
    mut v___y_3542_: *mut crate::leanh::LeanObject,
    mut v___y_3543_: *mut crate::leanh::LeanObject,
    mut v___y_3544_: *mut crate::leanh::LeanObject,
    mut v___y_3545_: *mut crate::leanh::LeanObject,
    mut v___y_3546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3547_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg(v_indVal_3535_, v_allIndVals_3536_, v_ctx_3537_, v_as_x27_3538_, v_b_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
    crate::leanh::lean_dec(v___y_3545_);
    crate::leanh::lean_dec_ref(v___y_3544_);
    crate::leanh::lean_dec(v___y_3543_);
    crate::leanh::lean_dec_ref(v___y_3542_);
    crate::leanh::lean_dec(v___y_3541_);
    crate::leanh::lean_dec_ref(v___y_3540_);
    crate::leanh::lean_dec(v_as_x27_3538_);
    return v_res_3547_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__7(
    mut v_sz_3548_: usize,
    mut v_i_3549_: usize,
    mut v_bs_3550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3551_: u8 = 0;
    let mut v_v_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: usize = 0;
    let mut v___x_3556_: usize = 0;
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3551_ = lean_usize_dec_lt(v_i_3549_, v_sz_3548_);
                if v___x_3551_ == 0 {
                    return v_bs_3550_;
                } else {
                    v_v_3552_ = lean_array_uget(v_bs_3550_, v_i_3549_);
                    v___x_3553_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3554_ = lean_array_uset(v_bs_3550_, v_i_3549_, v___x_3553_);
                    v___x_3555_ = 1usize;
                    v___x_3556_ = lean_usize_add(v_i_3549_, v___x_3555_);
                    v___x_3557_ = lean_array_uset(v_bs_x27_3554_, v_i_3549_, v_v_3552_);
                    v_i_3549_ = v___x_3556_;
                    v_bs_3550_ = v___x_3557_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__7___boxed(
    mut v_sz_3559_: *mut crate::leanh::LeanObject,
    mut v_i_3560_: *mut crate::leanh::LeanObject,
    mut v_bs_3561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3562_: usize = 0;
    let mut v_i_boxed_3563_: usize = 0;
    let mut v_res_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3562_ = crate::leanh::lean_unbox_usize(v_sz_3559_);
    crate::leanh::lean_dec(v_sz_3559_);
    v_i_boxed_3563_ = crate::leanh::lean_unbox_usize(v_i_3560_);
    crate::leanh::lean_dec(v_i_3560_);
    v_res_3564_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__7(v_sz_boxed_3562_, v_i_boxed_3563_, v_bs_3561_);
    return v_res_3564_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts(
    mut v_ctx_3568_: *mut crate::leanh::LeanObject,
    mut v_indVal_3569_: *mut crate::leanh::LeanObject,
    mut v_a_3570_: *mut crate::leanh::LeanObject,
    mut v_a_3571_: *mut crate::leanh::LeanObject,
    mut v_a_3572_: *mut crate::leanh::LeanObject,
    mut v_a_3573_: *mut crate::leanh::LeanObject,
    mut v_a_3574_: *mut crate::leanh::LeanObject,
    mut v_a_3575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_all_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allIndVals_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3585_: u8 = 0;
    let mut v_fst_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3587_: usize = 0;
    let mut v___x_3588_: usize = 0;
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3593_: u8 = 0;
    let mut v_a_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3597_: u8 = 0;
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3601_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_all_3577_ = crate::leanh::lean_ctor_get(v_indVal_3569_, 3);
                v_ctors_3578_ = crate::leanh::lean_ctor_get(v_indVal_3569_, 4);
                crate::leanh::lean_inc(v_ctors_3578_);
                crate::leanh::lean_inc(v_all_3577_);
                v_allIndVals_3579_ = lean_array_mk(v_all_3577_);
                v___x_3580_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts___closed__0;
                v___x_3581_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg(v_indVal_3569_, v_allIndVals_3579_, v_ctx_3568_, v_ctors_3578_, v___x_3580_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_);
                crate::leanh::lean_dec(v_ctors_3578_);
                if crate::leanh::lean_obj_tag(v___x_3581_) == 0 {
                    v_a_3582_ = crate::leanh::lean_ctor_get(v___x_3581_, 0);
                    v_isSharedCheck_3593_ = (!crate::leanh::lean_is_exclusive(v___x_3581_)) as u8;
                    if v_isSharedCheck_3593_ == 0 {
                        v___x_3584_ = v___x_3581_;
                        v_isShared_3585_ = v_isSharedCheck_3593_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3582_);
                        crate::leanh::lean_dec(v___x_3581_);
                        v___x_3584_ = crate::leanh::lean_box(0);
                        v_isShared_3585_ = v_isSharedCheck_3593_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3594_ = crate::leanh::lean_ctor_get(v___x_3581_, 0);
                    v_isSharedCheck_3601_ = (!crate::leanh::lean_is_exclusive(v___x_3581_)) as u8;
                    if v_isSharedCheck_3601_ == 0 {
                        v___x_3596_ = v___x_3581_;
                        v_isShared_3597_ = v_isSharedCheck_3601_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3594_);
                        crate::leanh::lean_dec(v___x_3581_);
                        v___x_3596_ = crate::leanh::lean_box(0);
                        v_isShared_3597_ = v_isSharedCheck_3601_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3586_ = crate::leanh::lean_ctor_get(v_a_3582_, 0);
                crate::leanh::lean_inc(v_fst_3586_);
                crate::leanh::lean_dec(v_a_3582_);
                v_sz_3587_ = lean_array_size(v_fst_3586_);
                v___x_3588_ = 0usize;
                v___x_3589_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__7(v_sz_3587_, v___x_3588_, v_fst_3586_);
                if v_isShared_3585_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3584_, 0, v___x_3589_);
                    v___x_3591_ = v___x_3584_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3592_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3589_);
                    v___x_3591_ = v_reuseFailAlloc_3592_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3591_;
            }
            3 => {
                if v_isShared_3597_ == 0 {
                    v___x_3599_ = v___x_3596_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3600_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
                    v___x_3599_ = v_reuseFailAlloc_3600_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3599_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts___boxed(
    mut v_ctx_3602_: *mut crate::leanh::LeanObject,
    mut v_indVal_3603_: *mut crate::leanh::LeanObject,
    mut v_a_3604_: *mut crate::leanh::LeanObject,
    mut v_a_3605_: *mut crate::leanh::LeanObject,
    mut v_a_3606_: *mut crate::leanh::LeanObject,
    mut v_a_3607_: *mut crate::leanh::LeanObject,
    mut v_a_3608_: *mut crate::leanh::LeanObject,
    mut v_a_3609_: *mut crate::leanh::LeanObject,
    mut v_a_3610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3611_ =
        l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts(
            v_ctx_3602_,
            v_indVal_3603_,
            v_a_3604_,
            v_a_3605_,
            v_a_3606_,
            v_a_3607_,
            v_a_3608_,
            v_a_3609_,
        );
    crate::leanh::lean_dec(v_a_3609_);
    crate::leanh::lean_dec_ref(v_a_3608_);
    crate::leanh::lean_dec(v_a_3607_);
    crate::leanh::lean_dec_ref(v_a_3606_);
    crate::leanh::lean_dec(v_a_3605_);
    crate::leanh::lean_dec_ref(v_a_3604_);
    return v_res_3611_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3(
    mut v_upperBound_3612_: *mut crate::leanh::LeanObject,
    mut v___x_3613_: *mut crate::leanh::LeanObject,
    mut v_xs_3614_: *mut crate::leanh::LeanObject,
    mut v_allIndVals_3615_: *mut crate::leanh::LeanObject,
    mut v_ctx_3616_: *mut crate::leanh::LeanObject,
    mut v_inst_3617_: *mut crate::leanh::LeanObject,
    mut v_R_3618_: *mut crate::leanh::LeanObject,
    mut v_a_3619_: *mut crate::leanh::LeanObject,
    mut v_b_3620_: *mut crate::leanh::LeanObject,
    mut v_c_3621_: *mut crate::leanh::LeanObject,
    mut v___y_3622_: *mut crate::leanh::LeanObject,
    mut v___y_3623_: *mut crate::leanh::LeanObject,
    mut v___y_3624_: *mut crate::leanh::LeanObject,
    mut v___y_3625_: *mut crate::leanh::LeanObject,
    mut v___y_3626_: *mut crate::leanh::LeanObject,
    mut v___y_3627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3629_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg(v_upperBound_3612_, v___x_3613_, v_xs_3614_, v_allIndVals_3615_, v_ctx_3616_, v_a_3619_, v_b_3620_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
    return v___x_3629_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_3630_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_3631_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_xs_3632_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_allIndVals_3633_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_ctx_3634_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_3635_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_R_3636_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_3637_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_b_3638_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_c_3639_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_3640_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_3641_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_3642_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3643_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3644_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3645_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3646_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3647_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3(v_upperBound_3630_, v___x_3631_, v_xs_3632_, v_allIndVals_3633_, v_ctx_3634_, v_inst_3635_, v_R_3636_, v_a_3637_, v_b_3638_, v_c_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
    crate::leanh::lean_dec(v___y_3645_);
    crate::leanh::lean_dec_ref(v___y_3644_);
    crate::leanh::lean_dec(v___y_3643_);
    crate::leanh::lean_dec_ref(v___y_3642_);
    crate::leanh::lean_dec(v___y_3641_);
    crate::leanh::lean_dec_ref(v___y_3640_);
    crate::leanh::lean_dec_ref(v_ctx_3634_);
    crate::leanh::lean_dec_ref(v_allIndVals_3633_);
    crate::leanh::lean_dec_ref(v_xs_3632_);
    crate::leanh::lean_dec(v___x_3631_);
    crate::leanh::lean_dec(v_upperBound_3630_);
    return v_res_3647_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4(
    mut v_upperBound_3648_: *mut crate::leanh::LeanObject,
    mut v_inst_3649_: *mut crate::leanh::LeanObject,
    mut v_R_3650_: *mut crate::leanh::LeanObject,
    mut v_a_3651_: *mut crate::leanh::LeanObject,
    mut v_b_3652_: *mut crate::leanh::LeanObject,
    mut v_c_3653_: *mut crate::leanh::LeanObject,
    mut v___y_3654_: *mut crate::leanh::LeanObject,
    mut v___y_3655_: *mut crate::leanh::LeanObject,
    mut v___y_3656_: *mut crate::leanh::LeanObject,
    mut v___y_3657_: *mut crate::leanh::LeanObject,
    mut v___y_3658_: *mut crate::leanh::LeanObject,
    mut v___y_3659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3661_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___redArg(v_upperBound_3648_, v_a_3651_, v_b_3652_, v___y_3658_);
    return v___x_3661_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4___boxed(
    mut v_upperBound_3662_: *mut crate::leanh::LeanObject,
    mut v_inst_3663_: *mut crate::leanh::LeanObject,
    mut v_R_3664_: *mut crate::leanh::LeanObject,
    mut v_a_3665_: *mut crate::leanh::LeanObject,
    mut v_b_3666_: *mut crate::leanh::LeanObject,
    mut v_c_3667_: *mut crate::leanh::LeanObject,
    mut v___y_3668_: *mut crate::leanh::LeanObject,
    mut v___y_3669_: *mut crate::leanh::LeanObject,
    mut v___y_3670_: *mut crate::leanh::LeanObject,
    mut v___y_3671_: *mut crate::leanh::LeanObject,
    mut v___y_3672_: *mut crate::leanh::LeanObject,
    mut v___y_3673_: *mut crate::leanh::LeanObject,
    mut v___y_3674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3675_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__4(v_upperBound_3662_, v_inst_3663_, v_R_3664_, v_a_3665_, v_b_3666_, v_c_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_);
    crate::leanh::lean_dec(v___y_3673_);
    crate::leanh::lean_dec_ref(v___y_3672_);
    crate::leanh::lean_dec(v___y_3671_);
    crate::leanh::lean_dec_ref(v___y_3670_);
    crate::leanh::lean_dec(v___y_3669_);
    crate::leanh::lean_dec_ref(v___y_3668_);
    crate::leanh::lean_dec(v_upperBound_3662_);
    return v_res_3675_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6(
    mut v_indVal_3676_: *mut crate::leanh::LeanObject,
    mut v_allIndVals_3677_: *mut crate::leanh::LeanObject,
    mut v_ctx_3678_: *mut crate::leanh::LeanObject,
    mut v_as_3679_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3680_: *mut crate::leanh::LeanObject,
    mut v_b_3681_: *mut crate::leanh::LeanObject,
    mut v_a_3682_: *mut crate::leanh::LeanObject,
    mut v___y_3683_: *mut crate::leanh::LeanObject,
    mut v___y_3684_: *mut crate::leanh::LeanObject,
    mut v___y_3685_: *mut crate::leanh::LeanObject,
    mut v___y_3686_: *mut crate::leanh::LeanObject,
    mut v___y_3687_: *mut crate::leanh::LeanObject,
    mut v___y_3688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3690_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg(v_indVal_3676_, v_allIndVals_3677_, v_ctx_3678_, v_as_x27_3680_, v_b_3681_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
    return v___x_3690_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___boxed(
    mut v_indVal_3691_: *mut crate::leanh::LeanObject,
    mut v_allIndVals_3692_: *mut crate::leanh::LeanObject,
    mut v_ctx_3693_: *mut crate::leanh::LeanObject,
    mut v_as_3694_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3695_: *mut crate::leanh::LeanObject,
    mut v_b_3696_: *mut crate::leanh::LeanObject,
    mut v_a_3697_: *mut crate::leanh::LeanObject,
    mut v___y_3698_: *mut crate::leanh::LeanObject,
    mut v___y_3699_: *mut crate::leanh::LeanObject,
    mut v___y_3700_: *mut crate::leanh::LeanObject,
    mut v___y_3701_: *mut crate::leanh::LeanObject,
    mut v___y_3702_: *mut crate::leanh::LeanObject,
    mut v___y_3703_: *mut crate::leanh::LeanObject,
    mut v___y_3704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3705_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6(v_indVal_3691_, v_allIndVals_3692_, v_ctx_3693_, v_as_3694_, v_as_x27_3695_, v_b_3696_, v_a_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_);
    crate::leanh::lean_dec(v___y_3703_);
    crate::leanh::lean_dec_ref(v___y_3702_);
    crate::leanh::lean_dec(v___y_3701_);
    crate::leanh::lean_dec_ref(v___y_3700_);
    crate::leanh::lean_dec(v___y_3699_);
    crate::leanh::lean_dec_ref(v___y_3698_);
    crate::leanh::lean_dec(v_as_x27_3695_);
    crate::leanh::lean_dec(v_as_3694_);
    return v_res_3705_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0(
    mut v_00_u03b1_3706_: *mut crate::leanh::LeanObject,
    mut v_msg_3707_: *mut crate::leanh::LeanObject,
    mut v___y_3708_: *mut crate::leanh::LeanObject,
    mut v___y_3709_: *mut crate::leanh::LeanObject,
    mut v___y_3710_: *mut crate::leanh::LeanObject,
    mut v___y_3711_: *mut crate::leanh::LeanObject,
    mut v___y_3712_: *mut crate::leanh::LeanObject,
    mut v___y_3713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3715_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___redArg(v_msg_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
    return v___x_3715_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0___boxed(
    mut v_00_u03b1_3716_: *mut crate::leanh::LeanObject,
    mut v_msg_3717_: *mut crate::leanh::LeanObject,
    mut v___y_3718_: *mut crate::leanh::LeanObject,
    mut v___y_3719_: *mut crate::leanh::LeanObject,
    mut v___y_3720_: *mut crate::leanh::LeanObject,
    mut v___y_3721_: *mut crate::leanh::LeanObject,
    mut v___y_3722_: *mut crate::leanh::LeanObject,
    mut v___y_3723_: *mut crate::leanh::LeanObject,
    mut v___y_3724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3725_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0(v_00_u03b1_3716_, v_msg_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
    crate::leanh::lean_dec(v___y_3723_);
    crate::leanh::lean_dec_ref(v___y_3722_);
    crate::leanh::lean_dec(v___y_3721_);
    crate::leanh::lean_dec_ref(v___y_3720_);
    crate::leanh::lean_dec(v___y_3719_);
    crate::leanh::lean_dec_ref(v___y_3718_);
    return v_res_3725_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3(
    mut v_msgData_3726_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3727_: *mut crate::leanh::LeanObject,
    mut v___y_3728_: *mut crate::leanh::LeanObject,
    mut v___y_3729_: *mut crate::leanh::LeanObject,
    mut v___y_3730_: *mut crate::leanh::LeanObject,
    mut v___y_3731_: *mut crate::leanh::LeanObject,
    mut v___y_3732_: *mut crate::leanh::LeanObject,
    mut v___y_3733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3735_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_3726_, v_macroStack_3727_, v___y_3732_);
    return v___x_3735_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3___boxed(
    mut v_msgData_3736_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3737_: *mut crate::leanh::LeanObject,
    mut v___y_3738_: *mut crate::leanh::LeanObject,
    mut v___y_3739_: *mut crate::leanh::LeanObject,
    mut v___y_3740_: *mut crate::leanh::LeanObject,
    mut v___y_3741_: *mut crate::leanh::LeanObject,
    mut v___y_3742_: *mut crate::leanh::LeanObject,
    mut v___y_3743_: *mut crate::leanh::LeanObject,
    mut v___y_3744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3745_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__3(v_msgData_3736_, v_macroStack_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
    crate::leanh::lean_dec(v___y_3743_);
    crate::leanh::lean_dec_ref(v___y_3742_);
    crate::leanh::lean_dec(v___y_3741_);
    crate::leanh::lean_dec_ref(v___y_3740_);
    crate::leanh::lean_dec(v___y_3739_);
    crate::leanh::lean_dec_ref(v___y_3738_);
    return v_res_3745_;
}
pub unsafe fn l_Lean_Elab_Deriving_Hashable_mkMatch(
    mut v_ctx_3759_: *mut crate::leanh::LeanObject,
    mut v_header_3760_: *mut crate::leanh::LeanObject,
    mut v_indVal_3761_: *mut crate::leanh::LeanObject,
    mut v_a_3762_: *mut crate::leanh::LeanObject,
    mut v_a_3763_: *mut crate::leanh::LeanObject,
    mut v_a_3764_: *mut crate::leanh::LeanObject,
    mut v_a_3765_: *mut crate::leanh::LeanObject,
    mut v_a_3766_: *mut crate::leanh::LeanObject,
    mut v_a_3767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3775_: u8 = 0;
    let mut v_ref_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: u8 = 0;
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3785_: usize = 0;
    let mut v___x_3786_: usize = 0;
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3802_: u8 = 0;
    let mut v_a_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3806_: u8 = 0;
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3810_: u8 = 0;
    let mut v_a_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3814_: u8 = 0;
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3818_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_indVal_3761_);
                v___x_3769_ = l_Lean_Elab_Deriving_mkDiscrs(
                    v_header_3760_,
                    v_indVal_3761_,
                    v_a_3762_,
                    v_a_3763_,
                    v_a_3764_,
                    v_a_3765_,
                    v_a_3766_,
                    v_a_3767_,
                );
                if crate::leanh::lean_obj_tag(v___x_3769_) == 0 {
                    v_a_3770_ = crate::leanh::lean_ctor_get(v___x_3769_, 0);
                    crate::leanh::lean_inc(v_a_3770_);
                    crate::leanh::lean_dec_ref_known(v___x_3769_, 1);
                    v___x_3771_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts(v_ctx_3759_, v_indVal_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_);
                    if crate::leanh::lean_obj_tag(v___x_3771_) == 0 {
                        v_a_3772_ = crate::leanh::lean_ctor_get(v___x_3771_, 0);
                        v_isSharedCheck_3802_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3771_)) as u8;
                        if v_isSharedCheck_3802_ == 0 {
                            v___x_3774_ = v___x_3771_;
                            v_isShared_3775_ = v_isSharedCheck_3802_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3772_);
                            crate::leanh::lean_dec(v___x_3771_);
                            v___x_3774_ = crate::leanh::lean_box(0);
                            v_isShared_3775_ = v_isSharedCheck_3802_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3770_);
                        v_a_3803_ = crate::leanh::lean_ctor_get(v___x_3771_, 0);
                        v_isSharedCheck_3810_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3771_)) as u8;
                        if v_isSharedCheck_3810_ == 0 {
                            v___x_3805_ = v___x_3771_;
                            v_isShared_3806_ = v_isSharedCheck_3810_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3803_);
                            crate::leanh::lean_dec(v___x_3771_);
                            v___x_3805_ = crate::leanh::lean_box(0);
                            v_isShared_3806_ = v_isSharedCheck_3810_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_indVal_3761_);
                    crate::leanh::lean_dec_ref(v_ctx_3759_);
                    v_a_3811_ = crate::leanh::lean_ctor_get(v___x_3769_, 0);
                    v_isSharedCheck_3818_ = (!crate::leanh::lean_is_exclusive(v___x_3769_)) as u8;
                    if v_isSharedCheck_3818_ == 0 {
                        v___x_3813_ = v___x_3769_;
                        v_isShared_3814_ = v_isSharedCheck_3818_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3811_);
                        crate::leanh::lean_dec(v___x_3769_);
                        v___x_3813_ = crate::leanh::lean_box(0);
                        v_isShared_3814_ = v_isSharedCheck_3818_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_ref_3776_ = crate::leanh::lean_ctor_get(v_a_3766_, 5);
                v___x_3777_ = 0;
                v___x_3778_ = l_Lean_SourceInfo_fromRef(v_ref_3776_, v___x_3777_);
                v___x_3779_ = l_Lean_Elab_Deriving_Hashable_mkMatch___closed__0;
                v___x_3780_ = l_Lean_Elab_Deriving_Hashable_mkMatch___closed__1;
                crate::leanh::lean_inc_n(v___x_3778_, 6);
                v___x_3781_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3781_, 0, v___x_3778_);
                crate::leanh::lean_ctor_set(v___x_3781_, 1, v___x_3779_);
                v___x_3782_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10;
                v___x_3783_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3);
                v___x_3784_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3784_, 0, v___x_3778_);
                crate::leanh::lean_ctor_set(v___x_3784_, 1, v___x_3782_);
                crate::leanh::lean_ctor_set(v___x_3784_, 2, v___x_3783_);
                v_sz_3785_ = lean_array_size(v_a_3770_);
                v___x_3786_ = 0usize;
                v___x_3787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__1(v_sz_3785_, v___x_3786_, v_a_3770_);
                v___x_3788_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__8);
                v___x_3789_ = l_Lean_mkSepArray(v___x_3787_, v___x_3788_);
                crate::leanh::lean_dec_ref(v___x_3787_);
                v___x_3790_ = l_Array_append___redArg(v___x_3783_, v___x_3789_);
                crate::leanh::lean_dec_ref(v___x_3789_);
                v___x_3791_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3791_, 0, v___x_3778_);
                crate::leanh::lean_ctor_set(v___x_3791_, 1, v___x_3782_);
                crate::leanh::lean_ctor_set(v___x_3791_, 2, v___x_3790_);
                v___x_3792_ = l_Lean_Elab_Deriving_Hashable_mkMatch___closed__2;
                v___x_3793_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3793_, 0, v___x_3778_);
                crate::leanh::lean_ctor_set(v___x_3793_, 1, v___x_3792_);
                v___x_3794_ = l_Lean_Elab_Deriving_Hashable_mkMatch___closed__4;
                v___x_3795_ = l_Array_append___redArg(v___x_3783_, v_a_3772_);
                crate::leanh::lean_dec(v_a_3772_);
                v___x_3796_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3796_, 0, v___x_3778_);
                crate::leanh::lean_ctor_set(v___x_3796_, 1, v___x_3782_);
                crate::leanh::lean_ctor_set(v___x_3796_, 2, v___x_3795_);
                v___x_3797_ = l_Lean_Syntax_node1(v___x_3778_, v___x_3794_, v___x_3796_);
                crate::leanh::lean_inc_ref(v___x_3784_);
                v___x_3798_ = l_Lean_Syntax_node6(
                    v___x_3778_,
                    v___x_3780_,
                    v___x_3781_,
                    v___x_3784_,
                    v___x_3784_,
                    v___x_3791_,
                    v___x_3793_,
                    v___x_3797_,
                );
                if v_isShared_3775_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3774_, 0, v___x_3798_);
                    v___x_3800_ = v___x_3774_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3801_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3798_);
                    v___x_3800_ = v_reuseFailAlloc_3801_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3800_;
            }
            3 => {
                if v_isShared_3806_ == 0 {
                    v___x_3808_ = v___x_3805_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3809_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3803_);
                    v___x_3808_ = v_reuseFailAlloc_3809_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3808_;
            }
            5 => {
                if v_isShared_3814_ == 0 {
                    v___x_3816_ = v___x_3813_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3817_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
                    v___x_3816_ = v_reuseFailAlloc_3817_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3816_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_Hashable_mkMatch___boxed(
    mut v_ctx_3819_: *mut crate::leanh::LeanObject,
    mut v_header_3820_: *mut crate::leanh::LeanObject,
    mut v_indVal_3821_: *mut crate::leanh::LeanObject,
    mut v_a_3822_: *mut crate::leanh::LeanObject,
    mut v_a_3823_: *mut crate::leanh::LeanObject,
    mut v_a_3824_: *mut crate::leanh::LeanObject,
    mut v_a_3825_: *mut crate::leanh::LeanObject,
    mut v_a_3826_: *mut crate::leanh::LeanObject,
    mut v_a_3827_: *mut crate::leanh::LeanObject,
    mut v_a_3828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3829_ = l_Lean_Elab_Deriving_Hashable_mkMatch(
        v_ctx_3819_,
        v_header_3820_,
        v_indVal_3821_,
        v_a_3822_,
        v_a_3823_,
        v_a_3824_,
        v_a_3825_,
        v_a_3826_,
        v_a_3827_,
    );
    crate::leanh::lean_dec(v_a_3827_);
    crate::leanh::lean_dec_ref(v_a_3826_);
    crate::leanh::lean_dec(v_a_3825_);
    crate::leanh::lean_dec_ref(v_a_3824_);
    crate::leanh::lean_dec(v_a_3823_);
    crate::leanh::lean_dec_ref(v_a_3822_);
    return v_res_3829_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3869_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__14;
    v___x_3870_ = l_String_toRawSubstring_x27(v___x_3869_);
    return v___x_3870_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3901_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__28;
    v___x_3902_ = l_String_toRawSubstring_x27(v___x_3901_);
    return v___x_3902_;
}
pub unsafe fn l_Lean_Elab_Deriving_Hashable_mkAuxFunction(
    mut v_ctx_3945_: *mut crate::leanh::LeanObject,
    mut v_i_3946_: *mut crate::leanh::LeanObject,
    mut v_a_3947_: *mut crate::leanh::LeanObject,
    mut v_a_3948_: *mut crate::leanh::LeanObject,
    mut v_a_3949_: *mut crate::leanh::LeanObject,
    mut v_a_3950_: *mut crate::leanh::LeanObject,
    mut v_a_3951_: *mut crate::leanh::LeanObject,
    mut v_a_3952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_typeInfos_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxFunNames_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usePartial_3956_: u8 = 0;
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indVal_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3965_: u8 = 0;
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxFunName_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binders_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3974_: u8 = 0;
    let mut v_ref_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4037_: u8 = 0;
    let mut v_unused_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binders_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4044_: u8 = 0;
    let mut v_ref_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: u8 = 0;
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4094_: u8 = 0;
    let mut v_unused_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_argNames_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4107_: u8 = 0;
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4111_: u8 = 0;
    let mut v_isSharedCheck_4112_: u8 = 0;
    let mut v_a_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4116_: u8 = 0;
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_typeInfos_3954_ = crate::leanh::lean_ctor_get(v_ctx_3945_, 1);
                v_auxFunNames_3955_ = crate::leanh::lean_ctor_get(v_ctx_3945_, 2);
                v_usePartial_3956_ = crate::leanh::lean_ctor_get_uint8(
                    v_ctx_3945_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v___x_3957_ = l_Lean_instInhabitedInductiveVal_default;
                v_indVal_3958_ = lean_array_get_borrowed(v___x_3957_, v_typeInfos_3954_, v_i_3946_);
                crate::leanh::lean_inc(v_indVal_3958_);
                v___x_3959_ = l_Lean_Elab_Deriving_Hashable_mkHashableHeader(
                    v_indVal_3958_,
                    v_a_3947_,
                    v_a_3948_,
                    v_a_3949_,
                    v_a_3950_,
                    v_a_3951_,
                    v_a_3952_,
                );
                if crate::leanh::lean_obj_tag(v___x_3959_) == 0 {
                    v_a_3960_ = crate::leanh::lean_ctor_get(v___x_3959_, 0);
                    crate::leanh::lean_inc_n(v_a_3960_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_3959_, 1);
                    crate::leanh::lean_inc(v_indVal_3958_);
                    crate::leanh::lean_inc_ref(v_ctx_3945_);
                    v___x_3961_ = l_Lean_Elab_Deriving_Hashable_mkMatch(
                        v_ctx_3945_,
                        v_a_3960_,
                        v_indVal_3958_,
                        v_a_3947_,
                        v_a_3948_,
                        v_a_3949_,
                        v_a_3950_,
                        v_a_3951_,
                        v_a_3952_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3961_) == 0 {
                        v_a_3962_ = crate::leanh::lean_ctor_get(v___x_3961_, 0);
                        v_isSharedCheck_4112_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3961_)) as u8;
                        if v_isSharedCheck_4112_ == 0 {
                            v___x_3964_ = v___x_3961_;
                            v_isShared_3965_ = v_isSharedCheck_4112_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3962_);
                            crate::leanh::lean_dec(v___x_3961_);
                            v___x_3964_ = crate::leanh::lean_box(0);
                            v_isShared_3965_ = v_isSharedCheck_4112_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3960_);
                        crate::leanh::lean_dec_ref(v_ctx_3945_);
                        return v___x_3961_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_ctx_3945_);
                    v_a_4113_ = crate::leanh::lean_ctor_get(v___x_3959_, 0);
                    v_isSharedCheck_4120_ = (!crate::leanh::lean_is_exclusive(v___x_3959_)) as u8;
                    if v_isSharedCheck_4120_ == 0 {
                        v___x_4115_ = v___x_3959_;
                        v_isShared_4116_ = v_isSharedCheck_4120_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4113_);
                        crate::leanh::lean_dec(v___x_3959_);
                        v___x_4115_ = crate::leanh::lean_box(0);
                        v_isShared_4116_ = v_isSharedCheck_4120_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3966_ = crate::leanh::lean_box(0);
                v_auxFunName_3967_ = lean_array_get(v___x_3966_, v_auxFunNames_3955_, v_i_3946_);
                if v_usePartial_3956_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_3945_);
                    v_body_3969_ = v_a_3962_;
                    v___y_3970_ = v_a_3951_;
                    state = 2;
                    continue;
                } else {
                    v_argNames_4098_ = crate::leanh::lean_ctor_get(v_a_3960_, 1);
                    v___x_4099_ = l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1;
                    crate::leanh::lean_inc_ref(v_argNames_4098_);
                    v___x_4100_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(
                        v_ctx_3945_,
                        v___x_4099_,
                        v_argNames_4098_,
                        v_a_3947_,
                        v_a_3948_,
                        v_a_3949_,
                        v_a_3950_,
                        v_a_3951_,
                        v_a_3952_,
                    );
                    crate::leanh::lean_dec_ref(v_ctx_3945_);
                    if crate::leanh::lean_obj_tag(v___x_4100_) == 0 {
                        v_a_4101_ = crate::leanh::lean_ctor_get(v___x_4100_, 0);
                        crate::leanh::lean_inc(v_a_4101_);
                        crate::leanh::lean_dec_ref_known(v___x_4100_, 1);
                        v___x_4102_ = l_Lean_Elab_Deriving_mkLet(
                            v_a_4101_, v_a_3962_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_,
                            v_a_3951_, v_a_3952_,
                        );
                        crate::leanh::lean_dec(v_a_4101_);
                        if crate::leanh::lean_obj_tag(v___x_4102_) == 0 {
                            v_a_4103_ = crate::leanh::lean_ctor_get(v___x_4102_, 0);
                            crate::leanh::lean_inc(v_a_4103_);
                            crate::leanh::lean_dec_ref_known(v___x_4102_, 1);
                            v_body_3969_ = v_a_4103_;
                            v___y_3970_ = v_a_3951_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_auxFunName_3967_);
                            crate::leanh::lean_del_object(v___x_3964_);
                            crate::leanh::lean_dec(v_a_3960_);
                            return v___x_4102_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_auxFunName_3967_);
                        crate::leanh::lean_del_object(v___x_3964_);
                        crate::leanh::lean_dec(v_a_3962_);
                        crate::leanh::lean_dec(v_a_3960_);
                        v_a_4104_ = crate::leanh::lean_ctor_get(v___x_4100_, 0);
                        v_isSharedCheck_4111_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4100_)) as u8;
                        if v_isSharedCheck_4111_ == 0 {
                            v___x_4106_ = v___x_4100_;
                            v_isShared_4107_ = v_isSharedCheck_4111_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4104_);
                            crate::leanh::lean_dec(v___x_4100_);
                            v___x_4106_ = crate::leanh::lean_box(0);
                            v_isShared_4107_ = v_isSharedCheck_4111_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_usePartial_3956_ == 0 {
                    v_binders_3971_ = crate::leanh::lean_ctor_get(v_a_3960_, 0);
                    v_isSharedCheck_4037_ = (!crate::leanh::lean_is_exclusive(v_a_3960_)) as u8;
                    if v_isSharedCheck_4037_ == 0 {
                        v_unused_4038_ = crate::leanh::lean_ctor_get(v_a_3960_, 3);
                        crate::leanh::lean_dec(v_unused_4038_);
                        v_unused_4039_ = crate::leanh::lean_ctor_get(v_a_3960_, 2);
                        crate::leanh::lean_dec(v_unused_4039_);
                        v_unused_4040_ = crate::leanh::lean_ctor_get(v_a_3960_, 1);
                        crate::leanh::lean_dec(v_unused_4040_);
                        v___x_3973_ = v_a_3960_;
                        v_isShared_3974_ = v_isSharedCheck_4037_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_binders_3971_);
                        crate::leanh::lean_dec(v_a_3960_);
                        v___x_3973_ = crate::leanh::lean_box(0);
                        v_isShared_3974_ = v_isSharedCheck_4037_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_binders_4041_ = crate::leanh::lean_ctor_get(v_a_3960_, 0);
                    v_isSharedCheck_4094_ = (!crate::leanh::lean_is_exclusive(v_a_3960_)) as u8;
                    if v_isSharedCheck_4094_ == 0 {
                        v_unused_4095_ = crate::leanh::lean_ctor_get(v_a_3960_, 3);
                        crate::leanh::lean_dec(v_unused_4095_);
                        v_unused_4096_ = crate::leanh::lean_ctor_get(v_a_3960_, 2);
                        crate::leanh::lean_dec(v_unused_4096_);
                        v_unused_4097_ = crate::leanh::lean_ctor_get(v_a_3960_, 1);
                        crate::leanh::lean_dec(v_unused_4097_);
                        v___x_4043_ = v_a_3960_;
                        v_isShared_4044_ = v_isSharedCheck_4094_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_binders_4041_);
                        crate::leanh::lean_dec(v_a_3960_);
                        v___x_4043_ = crate::leanh::lean_box(0);
                        v_isShared_4044_ = v_isSharedCheck_4094_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v_ref_3975_ = crate::leanh::lean_ctor_get(v___y_3970_, 5);
                v_quotContext_3976_ = crate::leanh::lean_ctor_get(v___y_3970_, 10);
                v_currMacroScope_3977_ = crate::leanh::lean_ctor_get(v___y_3970_, 11);
                v___x_3978_ = l_Lean_SourceInfo_fromRef(v_ref_3975_, v_usePartial_3956_);
                v___x_3979_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1;
                v___x_3980_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3;
                v___x_3981_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10;
                v___x_3982_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3);
                crate::leanh::lean_inc_n(v___x_3978_, 4);
                v___x_3983_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3983_, 0, v___x_3978_);
                crate::leanh::lean_ctor_set(v___x_3983_, 1, v___x_3981_);
                crate::leanh::lean_ctor_set(v___x_3983_, 2, v___x_3982_);
                v___x_3984_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__5;
                v___x_3985_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__6;
                v___x_3986_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3986_, 0, v___x_3978_);
                crate::leanh::lean_ctor_set(v___x_3986_, 1, v___x_3985_);
                v___x_3987_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__8;
                v___x_3988_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__10;
                crate::leanh::lean_inc_ref(v___x_3983_);
                v___x_3989_ = l_Lean_Syntax_node1(v___x_3978_, v___x_3988_, v___x_3983_);
                v___x_3990_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__13;
                v___x_3991_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15_once
                    ),
                    _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__15,
                );
                v___x_3992_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__16;
                crate::leanh::lean_inc(v_currMacroScope_3977_);
                crate::leanh::lean_inc(v_quotContext_3976_);
                v___x_3993_ =
                    l_Lean_addMacroScope(v_quotContext_3976_, v___x_3992_, v_currMacroScope_3977_);
                v___x_3994_ = crate::leanh::lean_box(0);
                if v_isShared_3974_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3973_, 3);
                    crate::leanh::lean_ctor_set(v___x_3973_, 3, v___x_3994_);
                    crate::leanh::lean_ctor_set(v___x_3973_, 2, v___x_3993_);
                    crate::leanh::lean_ctor_set(v___x_3973_, 1, v___x_3991_);
                    crate::leanh::lean_ctor_set(v___x_3973_, 0, v___x_3978_);
                    v___x_3996_ = v___x_3973_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4036_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_3978_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4036_, 1, v___x_3991_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4036_, 2, v___x_3993_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4036_, 3, v___x_3994_);
                    v___x_3996_ = v_reuseFailAlloc_4036_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref_n(v___x_3983_, 11);
                crate::leanh::lean_inc_n(v___x_3978_, 19);
                v___x_3997_ =
                    l_Lean_Syntax_node2(v___x_3978_, v___x_3990_, v___x_3996_, v___x_3983_);
                v___x_3998_ =
                    l_Lean_Syntax_node2(v___x_3978_, v___x_3987_, v___x_3989_, v___x_3997_);
                v___x_3999_ = l_Lean_Syntax_node1(v___x_3978_, v___x_3981_, v___x_3998_);
                v___x_4000_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__17;
                v___x_4001_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4001_, 0, v___x_3978_);
                crate::leanh::lean_ctor_set(v___x_4001_, 1, v___x_4000_);
                v___x_4002_ = l_Lean_Syntax_node3(
                    v___x_3978_,
                    v___x_3984_,
                    v___x_3986_,
                    v___x_3999_,
                    v___x_4001_,
                );
                v___x_4003_ = l_Lean_Syntax_node1(v___x_3978_, v___x_3981_, v___x_4002_);
                v___x_4004_ = l_Lean_Syntax_node7(
                    v___x_3978_,
                    v___x_3980_,
                    v___x_3983_,
                    v___x_4003_,
                    v___x_3983_,
                    v___x_3983_,
                    v___x_3983_,
                    v___x_3983_,
                    v___x_3983_,
                );
                v___x_4005_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19;
                v___x_4006_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__20;
                v___x_4007_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4007_, 0, v___x_3978_);
                crate::leanh::lean_ctor_set(v___x_4007_, 1, v___x_4006_);
                v___x_4008_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22;
                v___x_4009_ = lean_mk_syntax_ident(v_auxFunName_3967_);
                v___x_4010_ =
                    l_Lean_Syntax_node2(v___x_3978_, v___x_4008_, v___x_4009_, v___x_3983_);
                v___x_4011_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24;
                v___x_4012_ = l_Array_append___redArg(v___x_3982_, v_binders_3971_);
                crate::leanh::lean_dec_ref(v_binders_3971_);
                v___x_4013_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4013_, 0, v___x_3978_);
                crate::leanh::lean_ctor_set(v___x_4013_, 1, v___x_3981_);
                crate::leanh::lean_ctor_set(v___x_4013_, 2, v___x_4012_);
                v___x_4014_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26;
                v___x_4015_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__27;
                v___x_4016_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4016_, 0, v___x_3978_);
                crate::leanh::lean_ctor_set(v___x_4016_, 1, v___x_4015_);
                v___x_4017_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29_once
                    ),
                    _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29,
                );
                v___x_4018_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30;
                crate::leanh::lean_inc(v_currMacroScope_3977_);
                crate::leanh::lean_inc(v_quotContext_3976_);
                v___x_4019_ =
                    l_Lean_addMacroScope(v_quotContext_3976_, v___x_4018_, v_currMacroScope_3977_);
                v___x_4020_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__34;
                v___x_4021_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4021_, 0, v___x_3978_);
                crate::leanh::lean_ctor_set(v___x_4021_, 1, v___x_4017_);
                crate::leanh::lean_ctor_set(v___x_4021_, 2, v___x_4019_);
                crate::leanh::lean_ctor_set(v___x_4021_, 3, v___x_4020_);
                v___x_4022_ =
                    l_Lean_Syntax_node2(v___x_3978_, v___x_4014_, v___x_4016_, v___x_4021_);
                v___x_4023_ = l_Lean_Syntax_node1(v___x_3978_, v___x_3981_, v___x_4022_);
                v___x_4024_ =
                    l_Lean_Syntax_node2(v___x_3978_, v___x_4011_, v___x_4013_, v___x_4023_);
                v___x_4025_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36;
                v___x_4026_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37;
                v___x_4027_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4027_, 0, v___x_3978_);
                crate::leanh::lean_ctor_set(v___x_4027_, 1, v___x_4026_);
                v___x_4028_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40;
                v___x_4029_ =
                    l_Lean_Syntax_node2(v___x_3978_, v___x_4028_, v___x_3983_, v___x_3983_);
                v___x_4030_ = l_Lean_Syntax_node4(
                    v___x_3978_,
                    v___x_4025_,
                    v___x_4027_,
                    v_body_3969_,
                    v___x_4029_,
                    v___x_3983_,
                );
                v___x_4031_ = l_Lean_Syntax_node5(
                    v___x_3978_,
                    v___x_4005_,
                    v___x_4007_,
                    v___x_4010_,
                    v___x_4024_,
                    v___x_4030_,
                    v___x_3983_,
                );
                v___x_4032_ =
                    l_Lean_Syntax_node2(v___x_3978_, v___x_3979_, v___x_4004_, v___x_4031_);
                if v_isShared_3965_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3964_, 0, v___x_4032_);
                    v___x_4034_ = v___x_3964_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4035_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4035_, 0, v___x_4032_);
                    v___x_4034_ = v_reuseFailAlloc_4035_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4034_;
            }
            6 => {
                v_ref_4045_ = crate::leanh::lean_ctor_get(v___y_3970_, 5);
                v_quotContext_4046_ = crate::leanh::lean_ctor_get(v___y_3970_, 10);
                v_currMacroScope_4047_ = crate::leanh::lean_ctor_get(v___y_3970_, 11);
                v___x_4048_ = 0;
                v___x_4049_ = l_Lean_SourceInfo_fromRef(v_ref_4045_, v___x_4048_);
                v___x_4050_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__1;
                v___x_4051_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__3;
                v___x_4052_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10;
                v___x_4053_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3);
                crate::leanh::lean_inc_n(v___x_4049_, 10);
                v___x_4054_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4054_, 0, v___x_4049_);
                crate::leanh::lean_ctor_set(v___x_4054_, 1, v___x_4052_);
                crate::leanh::lean_ctor_set(v___x_4054_, 2, v___x_4053_);
                v___x_4055_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__41;
                v___x_4056_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__42;
                v___x_4057_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4057_, 0, v___x_4049_);
                crate::leanh::lean_ctor_set(v___x_4057_, 1, v___x_4055_);
                v___x_4058_ = l_Lean_Syntax_node1(v___x_4049_, v___x_4056_, v___x_4057_);
                v___x_4059_ = l_Lean_Syntax_node1(v___x_4049_, v___x_4052_, v___x_4058_);
                crate::leanh::lean_inc_ref_n(v___x_4054_, 7);
                v___x_4060_ = l_Lean_Syntax_node7(
                    v___x_4049_,
                    v___x_4051_,
                    v___x_4054_,
                    v___x_4054_,
                    v___x_4054_,
                    v___x_4054_,
                    v___x_4054_,
                    v___x_4054_,
                    v___x_4059_,
                );
                v___x_4061_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__19;
                v___x_4062_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__20;
                v___x_4063_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4063_, 0, v___x_4049_);
                crate::leanh::lean_ctor_set(v___x_4063_, 1, v___x_4062_);
                v___x_4064_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__22;
                v___x_4065_ = lean_mk_syntax_ident(v_auxFunName_3967_);
                v___x_4066_ =
                    l_Lean_Syntax_node2(v___x_4049_, v___x_4064_, v___x_4065_, v___x_4054_);
                v___x_4067_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__24;
                v___x_4068_ = l_Array_append___redArg(v___x_4053_, v_binders_4041_);
                crate::leanh::lean_dec_ref(v_binders_4041_);
                v___x_4069_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4069_, 0, v___x_4049_);
                crate::leanh::lean_ctor_set(v___x_4069_, 1, v___x_4052_);
                crate::leanh::lean_ctor_set(v___x_4069_, 2, v___x_4068_);
                v___x_4070_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__26;
                v___x_4071_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__27;
                v___x_4072_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4072_, 0, v___x_4049_);
                crate::leanh::lean_ctor_set(v___x_4072_, 1, v___x_4071_);
                v___x_4073_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29_once
                    ),
                    _init_l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__29,
                );
                v___x_4074_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__30;
                crate::leanh::lean_inc(v_currMacroScope_4047_);
                crate::leanh::lean_inc(v_quotContext_4046_);
                v___x_4075_ =
                    l_Lean_addMacroScope(v_quotContext_4046_, v___x_4074_, v_currMacroScope_4047_);
                v___x_4076_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__45;
                if v_isShared_4044_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4043_, 3);
                    crate::leanh::lean_ctor_set(v___x_4043_, 3, v___x_4076_);
                    crate::leanh::lean_ctor_set(v___x_4043_, 2, v___x_4075_);
                    crate::leanh::lean_ctor_set(v___x_4043_, 1, v___x_4073_);
                    crate::leanh::lean_ctor_set(v___x_4043_, 0, v___x_4049_);
                    v___x_4078_ = v___x_4043_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4093_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_4049_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 1, v___x_4073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 2, v___x_4075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 3, v___x_4076_);
                    v___x_4078_ = v_reuseFailAlloc_4093_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_inc_n(v___x_4049_, 7);
                v___x_4079_ =
                    l_Lean_Syntax_node2(v___x_4049_, v___x_4070_, v___x_4072_, v___x_4078_);
                v___x_4080_ = l_Lean_Syntax_node1(v___x_4049_, v___x_4052_, v___x_4079_);
                v___x_4081_ =
                    l_Lean_Syntax_node2(v___x_4049_, v___x_4067_, v___x_4069_, v___x_4080_);
                v___x_4082_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__36;
                v___x_4083_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__37;
                v___x_4084_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4084_, 0, v___x_4049_);
                crate::leanh::lean_ctor_set(v___x_4084_, 1, v___x_4083_);
                v___x_4085_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction___closed__40;
                crate::leanh::lean_inc_ref_n(v___x_4054_, 3);
                v___x_4086_ =
                    l_Lean_Syntax_node2(v___x_4049_, v___x_4085_, v___x_4054_, v___x_4054_);
                v___x_4087_ = l_Lean_Syntax_node4(
                    v___x_4049_,
                    v___x_4082_,
                    v___x_4084_,
                    v_body_3969_,
                    v___x_4086_,
                    v___x_4054_,
                );
                v___x_4088_ = l_Lean_Syntax_node5(
                    v___x_4049_,
                    v___x_4061_,
                    v___x_4063_,
                    v___x_4066_,
                    v___x_4081_,
                    v___x_4087_,
                    v___x_4054_,
                );
                v___x_4089_ =
                    l_Lean_Syntax_node2(v___x_4049_, v___x_4050_, v___x_4060_, v___x_4088_);
                if v_isShared_3965_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3964_, 0, v___x_4089_);
                    v___x_4091_ = v___x_3964_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4092_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___x_4089_);
                    v___x_4091_ = v_reuseFailAlloc_4092_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4091_;
            }
            9 => {
                if v_isShared_4107_ == 0 {
                    v___x_4109_ = v___x_4106_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4110_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
                    v___x_4109_ = v_reuseFailAlloc_4110_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4109_;
            }
            11 => {
                if v_isShared_4116_ == 0 {
                    v___x_4118_ = v___x_4115_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4119_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_a_4113_);
                    v___x_4118_ = v_reuseFailAlloc_4119_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4118_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_Hashable_mkAuxFunction___boxed(
    mut v_ctx_4121_: *mut crate::leanh::LeanObject,
    mut v_i_4122_: *mut crate::leanh::LeanObject,
    mut v_a_4123_: *mut crate::leanh::LeanObject,
    mut v_a_4124_: *mut crate::leanh::LeanObject,
    mut v_a_4125_: *mut crate::leanh::LeanObject,
    mut v_a_4126_: *mut crate::leanh::LeanObject,
    mut v_a_4127_: *mut crate::leanh::LeanObject,
    mut v_a_4128_: *mut crate::leanh::LeanObject,
    mut v_a_4129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4130_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction(
        v_ctx_4121_,
        v_i_4122_,
        v_a_4123_,
        v_a_4124_,
        v_a_4125_,
        v_a_4126_,
        v_a_4127_,
        v_a_4128_,
    );
    crate::leanh::lean_dec(v_a_4128_);
    crate::leanh::lean_dec_ref(v_a_4127_);
    crate::leanh::lean_dec(v_a_4126_);
    crate::leanh::lean_dec_ref(v_a_4125_);
    crate::leanh::lean_dec(v_a_4124_);
    crate::leanh::lean_dec_ref(v_a_4123_);
    crate::leanh::lean_dec(v_i_4122_);
    return v_res_4130_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg(
    mut v_upperBound_4131_: *mut crate::leanh::LeanObject,
    mut v_ctx_4132_: *mut crate::leanh::LeanObject,
    mut v_a_4133_: *mut crate::leanh::LeanObject,
    mut v_b_4134_: *mut crate::leanh::LeanObject,
    mut v___y_4135_: *mut crate::leanh::LeanObject,
    mut v___y_4136_: *mut crate::leanh::LeanObject,
    mut v___y_4137_: *mut crate::leanh::LeanObject,
    mut v___y_4138_: *mut crate::leanh::LeanObject,
    mut v___y_4139_: *mut crate::leanh::LeanObject,
    mut v___y_4140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4142_: u8 = 0;
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4153_: u8 = 0;
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4157_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4142_ = lean_nat_dec_lt(v_a_4133_, v_upperBound_4131_);
                if v___x_4142_ == 0 {
                    crate::leanh::lean_dec(v_a_4133_);
                    crate::leanh::lean_dec_ref(v_ctx_4132_);
                    v___x_4143_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4143_, 0, v_b_4134_);
                    return v___x_4143_;
                } else {
                    crate::leanh::lean_inc_ref(v_ctx_4132_);
                    v___x_4144_ = l_Lean_Elab_Deriving_Hashable_mkAuxFunction(
                        v_ctx_4132_,
                        v_a_4133_,
                        v___y_4135_,
                        v___y_4136_,
                        v___y_4137_,
                        v___y_4138_,
                        v___y_4139_,
                        v___y_4140_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4144_) == 0 {
                        v_a_4145_ = crate::leanh::lean_ctor_get(v___x_4144_, 0);
                        crate::leanh::lean_inc(v_a_4145_);
                        crate::leanh::lean_dec_ref_known(v___x_4144_, 1);
                        v___x_4146_ = lean_array_push(v_b_4134_, v_a_4145_);
                        v___x_4147_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4148_ = lean_nat_add(v_a_4133_, v___x_4147_);
                        crate::leanh::lean_dec(v_a_4133_);
                        v_a_4133_ = v___x_4148_;
                        v_b_4134_ = v___x_4146_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_4134_);
                        crate::leanh::lean_dec(v_a_4133_);
                        crate::leanh::lean_dec_ref(v_ctx_4132_);
                        v_a_4150_ = crate::leanh::lean_ctor_get(v___x_4144_, 0);
                        v_isSharedCheck_4157_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4144_)) as u8;
                        if v_isSharedCheck_4157_ == 0 {
                            v___x_4152_ = v___x_4144_;
                            v_isShared_4153_ = v_isSharedCheck_4157_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4150_);
                            crate::leanh::lean_dec(v___x_4144_);
                            v___x_4152_ = crate::leanh::lean_box(0);
                            v_isShared_4153_ = v_isSharedCheck_4157_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4153_ == 0 {
                    v___x_4155_ = v___x_4152_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4156_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
                    v___x_4155_ = v_reuseFailAlloc_4156_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4155_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg___boxed(
    mut v_upperBound_4158_: *mut crate::leanh::LeanObject,
    mut v_ctx_4159_: *mut crate::leanh::LeanObject,
    mut v_a_4160_: *mut crate::leanh::LeanObject,
    mut v_b_4161_: *mut crate::leanh::LeanObject,
    mut v___y_4162_: *mut crate::leanh::LeanObject,
    mut v___y_4163_: *mut crate::leanh::LeanObject,
    mut v___y_4164_: *mut crate::leanh::LeanObject,
    mut v___y_4165_: *mut crate::leanh::LeanObject,
    mut v___y_4166_: *mut crate::leanh::LeanObject,
    mut v___y_4167_: *mut crate::leanh::LeanObject,
    mut v___y_4168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4169_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg(v_upperBound_4158_, v_ctx_4159_, v_a_4160_, v_b_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_);
    crate::leanh::lean_dec(v___y_4167_);
    crate::leanh::lean_dec_ref(v___y_4166_);
    crate::leanh::lean_dec(v___y_4165_);
    crate::leanh::lean_dec_ref(v___y_4164_);
    crate::leanh::lean_dec(v___y_4163_);
    crate::leanh::lean_dec_ref(v___y_4162_);
    crate::leanh::lean_dec(v_upperBound_4158_);
    return v_res_4169_;
}
pub unsafe fn l_Lean_Elab_Deriving_Hashable_mkHashFuncs(
    mut v_ctx_4177_: *mut crate::leanh::LeanObject,
    mut v_a_4178_: *mut crate::leanh::LeanObject,
    mut v_a_4179_: *mut crate::leanh::LeanObject,
    mut v_a_4180_: *mut crate::leanh::LeanObject,
    mut v_a_4181_: *mut crate::leanh::LeanObject,
    mut v_a_4182_: *mut crate::leanh::LeanObject,
    mut v_a_4183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_typeInfos_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDefs_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4193_: u8 = 0;
    let mut v_ref_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: u8 = 0;
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4210_: u8 = 0;
    let mut v_a_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4214_: u8 = 0;
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4218_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_typeInfos_4185_ = crate::leanh::lean_ctor_get(v_ctx_4177_, 1);
                v___x_4186_ = lean_array_get_size(v_typeInfos_4185_);
                v___x_4187_ = crate::leanh::lean_unsigned_to_nat(0);
                v_auxDefs_4188_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___closed__1;
                v___x_4189_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg(v___x_4186_, v_ctx_4177_, v___x_4187_, v_auxDefs_4188_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_);
                if crate::leanh::lean_obj_tag(v___x_4189_) == 0 {
                    v_a_4190_ = crate::leanh::lean_ctor_get(v___x_4189_, 0);
                    v_isSharedCheck_4210_ = (!crate::leanh::lean_is_exclusive(v___x_4189_)) as u8;
                    if v_isSharedCheck_4210_ == 0 {
                        v___x_4192_ = v___x_4189_;
                        v_isShared_4193_ = v_isSharedCheck_4210_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4190_);
                        crate::leanh::lean_dec(v___x_4189_);
                        v___x_4192_ = crate::leanh::lean_box(0);
                        v_isShared_4193_ = v_isSharedCheck_4210_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4211_ = crate::leanh::lean_ctor_get(v___x_4189_, 0);
                    v_isSharedCheck_4218_ = (!crate::leanh::lean_is_exclusive(v___x_4189_)) as u8;
                    if v_isSharedCheck_4218_ == 0 {
                        v___x_4213_ = v___x_4189_;
                        v_isShared_4214_ = v_isSharedCheck_4218_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4211_);
                        crate::leanh::lean_dec(v___x_4189_);
                        v___x_4213_ = crate::leanh::lean_box(0);
                        v_isShared_4214_ = v_isSharedCheck_4218_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_ref_4194_ = crate::leanh::lean_ctor_get(v_a_4182_, 5);
                v___x_4195_ = 0;
                v___x_4196_ = l_Lean_SourceInfo_fromRef(v_ref_4194_, v___x_4195_);
                v___x_4197_ = l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__0;
                v___x_4198_ = l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__1;
                crate::leanh::lean_inc_n(v___x_4196_, 3);
                v___x_4199_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4199_, 0, v___x_4196_);
                crate::leanh::lean_ctor_set(v___x_4199_, 1, v___x_4197_);
                v___x_4200_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__10;
                v___x_4201_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__6___redArg___lam__1___closed__3);
                v___x_4202_ = l_Array_append___redArg(v___x_4201_, v_a_4190_);
                crate::leanh::lean_dec(v_a_4190_);
                v___x_4203_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4203_, 0, v___x_4196_);
                crate::leanh::lean_ctor_set(v___x_4203_, 1, v___x_4200_);
                crate::leanh::lean_ctor_set(v___x_4203_, 2, v___x_4202_);
                v___x_4204_ = l_Lean_Elab_Deriving_Hashable_mkHashFuncs___closed__2;
                v___x_4205_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4205_, 0, v___x_4196_);
                crate::leanh::lean_ctor_set(v___x_4205_, 1, v___x_4204_);
                v___x_4206_ = l_Lean_Syntax_node3(
                    v___x_4196_,
                    v___x_4198_,
                    v___x_4199_,
                    v___x_4203_,
                    v___x_4205_,
                );
                if v_isShared_4193_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4192_, 0, v___x_4206_);
                    v___x_4208_ = v___x_4192_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4209_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4206_);
                    v___x_4208_ = v_reuseFailAlloc_4209_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4208_;
            }
            3 => {
                if v_isShared_4214_ == 0 {
                    v___x_4216_ = v___x_4213_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4217_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4211_);
                    v___x_4216_ = v_reuseFailAlloc_4217_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4216_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_Hashable_mkHashFuncs___boxed(
    mut v_ctx_4219_: *mut crate::leanh::LeanObject,
    mut v_a_4220_: *mut crate::leanh::LeanObject,
    mut v_a_4221_: *mut crate::leanh::LeanObject,
    mut v_a_4222_: *mut crate::leanh::LeanObject,
    mut v_a_4223_: *mut crate::leanh::LeanObject,
    mut v_a_4224_: *mut crate::leanh::LeanObject,
    mut v_a_4225_: *mut crate::leanh::LeanObject,
    mut v_a_4226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4227_ = l_Lean_Elab_Deriving_Hashable_mkHashFuncs(
        v_ctx_4219_,
        v_a_4220_,
        v_a_4221_,
        v_a_4222_,
        v_a_4223_,
        v_a_4224_,
        v_a_4225_,
    );
    crate::leanh::lean_dec(v_a_4225_);
    crate::leanh::lean_dec_ref(v_a_4224_);
    crate::leanh::lean_dec(v_a_4223_);
    crate::leanh::lean_dec_ref(v_a_4222_);
    crate::leanh::lean_dec(v_a_4221_);
    crate::leanh::lean_dec_ref(v_a_4220_);
    return v_res_4227_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0(
    mut v_upperBound_4228_: *mut crate::leanh::LeanObject,
    mut v_ctx_4229_: *mut crate::leanh::LeanObject,
    mut v_inst_4230_: *mut crate::leanh::LeanObject,
    mut v_R_4231_: *mut crate::leanh::LeanObject,
    mut v_a_4232_: *mut crate::leanh::LeanObject,
    mut v_b_4233_: *mut crate::leanh::LeanObject,
    mut v_c_4234_: *mut crate::leanh::LeanObject,
    mut v___y_4235_: *mut crate::leanh::LeanObject,
    mut v___y_4236_: *mut crate::leanh::LeanObject,
    mut v___y_4237_: *mut crate::leanh::LeanObject,
    mut v___y_4238_: *mut crate::leanh::LeanObject,
    mut v___y_4239_: *mut crate::leanh::LeanObject,
    mut v___y_4240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4242_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___redArg(v_upperBound_4228_, v_ctx_4229_, v_a_4232_, v_b_4233_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_);
    return v___x_4242_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0___boxed(
    mut v_upperBound_4243_: *mut crate::leanh::LeanObject,
    mut v_ctx_4244_: *mut crate::leanh::LeanObject,
    mut v_inst_4245_: *mut crate::leanh::LeanObject,
    mut v_R_4246_: *mut crate::leanh::LeanObject,
    mut v_a_4247_: *mut crate::leanh::LeanObject,
    mut v_b_4248_: *mut crate::leanh::LeanObject,
    mut v_c_4249_: *mut crate::leanh::LeanObject,
    mut v___y_4250_: *mut crate::leanh::LeanObject,
    mut v___y_4251_: *mut crate::leanh::LeanObject,
    mut v___y_4252_: *mut crate::leanh::LeanObject,
    mut v___y_4253_: *mut crate::leanh::LeanObject,
    mut v___y_4254_: *mut crate::leanh::LeanObject,
    mut v___y_4255_: *mut crate::leanh::LeanObject,
    mut v___y_4256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4257_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Hashable_mkHashFuncs_spec__0(
            v_upperBound_4243_,
            v_ctx_4244_,
            v_inst_4245_,
            v_R_4246_,
            v_a_4247_,
            v_b_4248_,
            v_c_4249_,
            v___y_4250_,
            v___y_4251_,
            v___y_4252_,
            v___y_4253_,
            v___y_4254_,
            v___y_4255_,
        );
    crate::leanh::lean_dec(v___y_4255_);
    crate::leanh::lean_dec_ref(v___y_4254_);
    crate::leanh::lean_dec(v___y_4253_);
    crate::leanh::lean_dec_ref(v___y_4252_);
    crate::leanh::lean_dec(v___y_4251_);
    crate::leanh::lean_dec_ref(v___y_4250_);
    crate::leanh::lean_dec(v_upperBound_4243_);
    return v_res_4257_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__0()
-> f64 {
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: f64 = 0.0;
    v___x_4258_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4259_ = lean_float_of_nat(v___x_4258_);
    return v___x_4259_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg(
    mut v_cls_4262_: *mut crate::leanh::LeanObject,
    mut v_msg_4263_: *mut crate::leanh::LeanObject,
    mut v___y_4264_: *mut crate::leanh::LeanObject,
    mut v___y_4265_: *mut crate::leanh::LeanObject,
    mut v___y_4266_: *mut crate::leanh::LeanObject,
    mut v___y_4267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4274_: u8 = 0;
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4287_: u8 = 0;
    let mut v_tid_4288_: u64 = 0;
    let mut v_traces_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4292_: u8 = 0;
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: f64 = 0.0;
    let mut v___x_4295_: u8 = 0;
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4313_: u8 = 0;
    let mut v_isSharedCheck_4314_: u8 = 0;
    let mut v_isSharedCheck_4315_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4269_ = crate::leanh::lean_ctor_get(v___y_4266_, 5);
                v___x_4270_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__0_spec__0_spec__2(v_msg_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
                v_a_4271_ = crate::leanh::lean_ctor_get(v___x_4270_, 0);
                v_isSharedCheck_4315_ = (!crate::leanh::lean_is_exclusive(v___x_4270_)) as u8;
                if v_isSharedCheck_4315_ == 0 {
                    v___x_4273_ = v___x_4270_;
                    v_isShared_4274_ = v_isSharedCheck_4315_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4271_);
                    crate::leanh::lean_dec(v___x_4270_);
                    v___x_4273_ = crate::leanh::lean_box(0);
                    v_isShared_4274_ = v_isSharedCheck_4315_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4275_ = lean_st_ref_take(v___y_4267_);
                v_traceState_4276_ = crate::leanh::lean_ctor_get(v___x_4275_, 4);
                v_env_4277_ = crate::leanh::lean_ctor_get(v___x_4275_, 0);
                v_nextMacroScope_4278_ = crate::leanh::lean_ctor_get(v___x_4275_, 1);
                v_ngen_4279_ = crate::leanh::lean_ctor_get(v___x_4275_, 2);
                v_auxDeclNGen_4280_ = crate::leanh::lean_ctor_get(v___x_4275_, 3);
                v_cache_4281_ = crate::leanh::lean_ctor_get(v___x_4275_, 5);
                v_messages_4282_ = crate::leanh::lean_ctor_get(v___x_4275_, 6);
                v_infoState_4283_ = crate::leanh::lean_ctor_get(v___x_4275_, 7);
                v_snapshotTasks_4284_ = crate::leanh::lean_ctor_get(v___x_4275_, 8);
                v_isSharedCheck_4314_ = (!crate::leanh::lean_is_exclusive(v___x_4275_)) as u8;
                if v_isSharedCheck_4314_ == 0 {
                    v___x_4286_ = v___x_4275_;
                    v_isShared_4287_ = v_isSharedCheck_4314_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4284_);
                    crate::leanh::lean_inc(v_infoState_4283_);
                    crate::leanh::lean_inc(v_messages_4282_);
                    crate::leanh::lean_inc(v_cache_4281_);
                    crate::leanh::lean_inc(v_traceState_4276_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4280_);
                    crate::leanh::lean_inc(v_ngen_4279_);
                    crate::leanh::lean_inc(v_nextMacroScope_4278_);
                    crate::leanh::lean_inc(v_env_4277_);
                    crate::leanh::lean_dec(v___x_4275_);
                    v___x_4286_ = crate::leanh::lean_box(0);
                    v_isShared_4287_ = v_isSharedCheck_4314_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4288_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_4276_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4289_ = crate::leanh::lean_ctor_get(v_traceState_4276_, 0);
                v_isSharedCheck_4313_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_4276_)) as u8;
                if v_isSharedCheck_4313_ == 0 {
                    v___x_4291_ = v_traceState_4276_;
                    v_isShared_4292_ = v_isSharedCheck_4313_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_4289_);
                    crate::leanh::lean_dec(v_traceState_4276_);
                    v___x_4291_ = crate::leanh::lean_box(0);
                    v_isShared_4292_ = v_isSharedCheck_4313_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4293_ = crate::leanh::lean_box(0);
                v___x_4294_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__0);
                v___x_4295_ = 0;
                v___x_4296_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__18;
                v___x_4297_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_4297_, 0, v_cls_4262_);
                crate::leanh::lean_ctor_set(v___x_4297_, 1, v___x_4293_);
                crate::leanh::lean_ctor_set(v___x_4297_, 2, v___x_4296_);
                crate::leanh::lean_ctor_set_float(
                    v___x_4297_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_4294_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_4297_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4294_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4297_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4295_,
                );
                v___x_4298_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___closed__1;
                v___x_4299_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4299_, 0, v___x_4297_);
                crate::leanh::lean_ctor_set(v___x_4299_, 1, v_a_4271_);
                crate::leanh::lean_ctor_set(v___x_4299_, 2, v___x_4298_);
                crate::leanh::lean_inc(v_ref_4269_);
                v___x_4300_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4300_, 0, v_ref_4269_);
                crate::leanh::lean_ctor_set(v___x_4300_, 1, v___x_4299_);
                v___x_4301_ = l_Lean_PersistentArray_push___redArg(v_traces_4289_, v___x_4300_);
                if v_isShared_4292_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4291_, 0, v___x_4301_);
                    v___x_4303_ = v___x_4291_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4312_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4312_, 0, v___x_4301_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4312_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_4288_,
                    );
                    v___x_4303_ = v_reuseFailAlloc_4312_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4287_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4286_, 4, v___x_4303_);
                    v___x_4305_ = v___x_4286_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4311_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_env_4277_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4311_, 1, v_nextMacroScope_4278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4311_, 2, v_ngen_4279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4311_, 3, v_auxDeclNGen_4280_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4311_, 4, v___x_4303_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4311_, 5, v_cache_4281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4311_, 6, v_messages_4282_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4311_, 7, v_infoState_4283_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4311_, 8, v_snapshotTasks_4284_);
                    v___x_4305_ = v_reuseFailAlloc_4311_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4306_ = lean_st_ref_set(v___y_4267_, v___x_4305_);
                v___x_4307_ = crate::leanh::lean_box(0);
                if v_isShared_4274_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4273_, 0, v___x_4307_);
                    v___x_4309_ = v___x_4273_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4310_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4310_, 0, v___x_4307_);
                    v___x_4309_ = v_reuseFailAlloc_4310_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg___boxed(
    mut v_cls_4316_: *mut crate::leanh::LeanObject,
    mut v_msg_4317_: *mut crate::leanh::LeanObject,
    mut v___y_4318_: *mut crate::leanh::LeanObject,
    mut v___y_4319_: *mut crate::leanh::LeanObject,
    mut v___y_4320_: *mut crate::leanh::LeanObject,
    mut v___y_4321_: *mut crate::leanh::LeanObject,
    mut v___y_4322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4323_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg(v_cls_4316_, v_msg_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
    crate::leanh::lean_dec(v___y_4321_);
    crate::leanh::lean_dec_ref(v___y_4320_);
    crate::leanh::lean_dec(v___y_4319_);
    crate::leanh::lean_dec_ref(v___y_4318_);
    return v_res_4323_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0(
    mut v_a_4324_: *mut crate::leanh::LeanObject,
    mut v_a_4325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4331_: u8 = 0;
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4337_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4324_) == 0 {
                    v___x_4326_ = l_List_reverse___redArg(v_a_4325_);
                    return v___x_4326_;
                } else {
                    v_head_4327_ = crate::leanh::lean_ctor_get(v_a_4324_, 0);
                    v_tail_4328_ = crate::leanh::lean_ctor_get(v_a_4324_, 1);
                    v_isSharedCheck_4337_ = (!crate::leanh::lean_is_exclusive(v_a_4324_)) as u8;
                    if v_isSharedCheck_4337_ == 0 {
                        v___x_4330_ = v_a_4324_;
                        v_isShared_4331_ = v_isSharedCheck_4337_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4328_);
                        crate::leanh::lean_inc(v_head_4327_);
                        crate::leanh::lean_dec(v_a_4324_);
                        v___x_4330_ = crate::leanh::lean_box(0);
                        v_isShared_4331_ = v_isSharedCheck_4337_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4332_ = l_Lean_MessageData_ofSyntax(v_head_4327_);
                if v_isShared_4331_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4330_, 1, v_a_4325_);
                    crate::leanh::lean_ctor_set(v___x_4330_, 0, v___x_4332_);
                    v___x_4334_ = v___x_4330_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4336_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4332_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 1, v_a_4325_);
                    v___x_4334_ = v_reuseFailAlloc_4336_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4324_ = v_tail_4328_;
                v_a_4325_ = v___x_4334_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4346_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1;
    v___x_4347_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__3;
    v___x_4348_ = l_Lean_Name_append(v___x_4347_, v___x_4346_);
    return v___x_4348_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4350_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__5;
    v___x_4351_ = l_Lean_stringToMessageData(v___x_4350_);
    return v___x_4351_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds(
    mut v_declName_4352_: *mut crate::leanh::LeanObject,
    mut v_a_4353_: *mut crate::leanh::LeanObject,
    mut v_a_4354_: *mut crate::leanh::LeanObject,
    mut v_a_4355_: *mut crate::leanh::LeanObject,
    mut v_a_4356_: *mut crate::leanh::LeanObject,
    mut v_a_4357_: *mut crate::leanh::LeanObject,
    mut v_a_4358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: u8 = 0;
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4375_: u8 = 0;
    let mut v_inheritedTraceOptions_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4377_: u8 = 0;
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: u8 = 0;
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4398_: u8 = 0;
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4402_: u8 = 0;
    let mut v_unused_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4407_: u8 = 0;
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4411_: u8 = 0;
    let mut v_isSharedCheck_4412_: u8 = 0;
    let mut v_a_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4416_: u8 = 0;
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4420_: u8 = 0;
    let mut v_a_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4424_: u8 = 0;
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4428_: u8 = 0;
    let mut v_a_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4432_: u8 = 0;
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4436_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4360_ = l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1;
                v___x_4361_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkMatch_mkAlts_spec__3___redArg___closed__36;
                v___x_4362_ = 1;
                crate::leanh::lean_inc(v_declName_4352_);
                v___x_4363_ = l_Lean_Elab_Deriving_mkContext(
                    v___x_4360_,
                    v___x_4361_,
                    v_declName_4352_,
                    v___x_4362_,
                    v_a_4353_,
                    v_a_4354_,
                    v_a_4355_,
                    v_a_4356_,
                    v_a_4357_,
                    v_a_4358_,
                );
                if crate::leanh::lean_obj_tag(v___x_4363_) == 0 {
                    v_a_4364_ = crate::leanh::lean_ctor_get(v___x_4363_, 0);
                    crate::leanh::lean_inc_n(v_a_4364_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_4363_, 1);
                    v___x_4365_ = l_Lean_Elab_Deriving_Hashable_mkHashFuncs(
                        v_a_4364_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4365_) == 0 {
                        v_a_4366_ = crate::leanh::lean_ctor_get(v___x_4365_, 0);
                        crate::leanh::lean_inc(v_a_4366_);
                        crate::leanh::lean_dec_ref_known(v___x_4365_, 1);
                        v___x_4367_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4368_ = lean_mk_empty_array_with_capacity(v___x_4367_);
                        crate::leanh::lean_inc_ref(v___x_4368_);
                        v___x_4369_ = lean_array_push(v___x_4368_, v_declName_4352_);
                        v___x_4370_ = l_Lean_Elab_Deriving_mkInstanceCmds(
                            v_a_4364_,
                            v___x_4360_,
                            v___x_4369_,
                            v___x_4362_,
                            v_a_4353_,
                            v_a_4354_,
                            v_a_4355_,
                            v_a_4356_,
                            v_a_4357_,
                            v_a_4358_,
                        );
                        crate::leanh::lean_dec_ref(v___x_4369_);
                        if crate::leanh::lean_obj_tag(v___x_4370_) == 0 {
                            v_options_4371_ = crate::leanh::lean_ctor_get(v_a_4357_, 2);
                            v_a_4372_ = crate::leanh::lean_ctor_get(v___x_4370_, 0);
                            v_isSharedCheck_4412_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4370_)) as u8;
                            if v_isSharedCheck_4412_ == 0 {
                                v___x_4374_ = v___x_4370_;
                                v_isShared_4375_ = v_isSharedCheck_4412_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4372_);
                                crate::leanh::lean_dec(v___x_4370_);
                                v___x_4374_ = crate::leanh::lean_box(0);
                                v_isShared_4375_ = v_isSharedCheck_4412_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4368_);
                            crate::leanh::lean_dec(v_a_4366_);
                            v_a_4413_ = crate::leanh::lean_ctor_get(v___x_4370_, 0);
                            v_isSharedCheck_4420_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4370_)) as u8;
                            if v_isSharedCheck_4420_ == 0 {
                                v___x_4415_ = v___x_4370_;
                                v_isShared_4416_ = v_isSharedCheck_4420_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4413_);
                                crate::leanh::lean_dec(v___x_4370_);
                                v___x_4415_ = crate::leanh::lean_box(0);
                                v_isShared_4416_ = v_isSharedCheck_4420_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4364_);
                        crate::leanh::lean_dec(v_declName_4352_);
                        v_a_4421_ = crate::leanh::lean_ctor_get(v___x_4365_, 0);
                        v_isSharedCheck_4428_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4365_)) as u8;
                        if v_isSharedCheck_4428_ == 0 {
                            v___x_4423_ = v___x_4365_;
                            v_isShared_4424_ = v_isSharedCheck_4428_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4421_);
                            crate::leanh::lean_dec(v___x_4365_);
                            v___x_4423_ = crate::leanh::lean_box(0);
                            v_isShared_4424_ = v_isSharedCheck_4428_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_4352_);
                    v_a_4429_ = crate::leanh::lean_ctor_get(v___x_4363_, 0);
                    v_isSharedCheck_4436_ = (!crate::leanh::lean_is_exclusive(v___x_4363_)) as u8;
                    if v_isSharedCheck_4436_ == 0 {
                        v___x_4431_ = v___x_4363_;
                        v_isShared_4432_ = v_isSharedCheck_4436_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4429_);
                        crate::leanh::lean_dec(v___x_4363_);
                        v___x_4431_ = crate::leanh::lean_box(0);
                        v_isShared_4432_ = v_isSharedCheck_4436_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v_inheritedTraceOptions_4376_ = crate::leanh::lean_ctor_get(v_a_4357_, 13);
                v_hasTrace_4377_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_4371_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_4378_ = lean_array_push(v___x_4368_, v_a_4366_);
                v___x_4379_ = l_Array_append___redArg(v___x_4378_, v_a_4372_);
                crate::leanh::lean_dec(v_a_4372_);
                if v_hasTrace_4377_ == 0 {
                    if v_isShared_4375_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4374_, 0, v___x_4379_);
                        v___x_4381_ = v___x_4374_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4382_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4379_);
                        v___x_4381_ = v_reuseFailAlloc_4382_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4383_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1;
                    v___x_4384_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__4_once), _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__4);
                    v___x_4385_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_4376_,
                        v_options_4371_,
                        v___x_4384_,
                    );
                    if v___x_4385_ == 0 {
                        if v_isShared_4375_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4374_, 0, v___x_4379_);
                            v___x_4387_ = v___x_4374_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4388_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4388_, 0, v___x_4379_);
                            v___x_4387_ = v_reuseFailAlloc_4388_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4374_);
                        v___x_4389_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__6_once), _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__6);
                        crate::leanh::lean_inc_ref(v___x_4379_);
                        v___x_4390_ = lean_array_to_list(v___x_4379_);
                        v___x_4391_ = crate::leanh::lean_box(0);
                        v___x_4392_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__0(v___x_4390_, v___x_4391_);
                        v___x_4393_ = l_Lean_MessageData_ofList(v___x_4392_);
                        v___x_4394_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4394_, 0, v___x_4389_);
                        crate::leanh::lean_ctor_set(v___x_4394_, 1, v___x_4393_);
                        v___x_4395_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg(v___x_4383_, v___x_4394_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
                        if crate::leanh::lean_obj_tag(v___x_4395_) == 0 {
                            v_isSharedCheck_4402_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4395_)) as u8;
                            if v_isSharedCheck_4402_ == 0 {
                                v_unused_4403_ = crate::leanh::lean_ctor_get(v___x_4395_, 0);
                                crate::leanh::lean_dec(v_unused_4403_);
                                v___x_4397_ = v___x_4395_;
                                v_isShared_4398_ = v_isSharedCheck_4402_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_4395_);
                                v___x_4397_ = crate::leanh::lean_box(0);
                                v_isShared_4398_ = v_isSharedCheck_4402_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4379_);
                            v_a_4404_ = crate::leanh::lean_ctor_get(v___x_4395_, 0);
                            v_isSharedCheck_4411_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4395_)) as u8;
                            if v_isSharedCheck_4411_ == 0 {
                                v___x_4406_ = v___x_4395_;
                                v_isShared_4407_ = v_isSharedCheck_4411_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4404_);
                                crate::leanh::lean_dec(v___x_4395_);
                                v___x_4406_ = crate::leanh::lean_box(0);
                                v_isShared_4407_ = v_isSharedCheck_4411_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_4381_;
            }
            3 => {
                return v___x_4387_;
            }
            4 => {
                if v_isShared_4398_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4397_, 0, v___x_4379_);
                    v___x_4400_ = v___x_4397_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4401_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4379_);
                    v___x_4400_ = v_reuseFailAlloc_4401_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4400_;
            }
            6 => {
                if v_isShared_4407_ == 0 {
                    v___x_4409_ = v___x_4406_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4410_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_a_4404_);
                    v___x_4409_ = v_reuseFailAlloc_4410_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4409_;
            }
            8 => {
                if v_isShared_4416_ == 0 {
                    v___x_4418_ = v___x_4415_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4419_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4413_);
                    v___x_4418_ = v_reuseFailAlloc_4419_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4418_;
            }
            10 => {
                if v_isShared_4424_ == 0 {
                    v___x_4426_ = v___x_4423_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4427_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_a_4421_);
                    v___x_4426_ = v_reuseFailAlloc_4427_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4426_;
            }
            12 => {
                if v_isShared_4432_ == 0 {
                    v___x_4434_ = v___x_4431_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4435_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
                    v___x_4434_ = v_reuseFailAlloc_4435_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4434_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___boxed(
    mut v_declName_4437_: *mut crate::leanh::LeanObject,
    mut v_a_4438_: *mut crate::leanh::LeanObject,
    mut v_a_4439_: *mut crate::leanh::LeanObject,
    mut v_a_4440_: *mut crate::leanh::LeanObject,
    mut v_a_4441_: *mut crate::leanh::LeanObject,
    mut v_a_4442_: *mut crate::leanh::LeanObject,
    mut v_a_4443_: *mut crate::leanh::LeanObject,
    mut v_a_4444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4445_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds(v_declName_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_);
    crate::leanh::lean_dec(v_a_4443_);
    crate::leanh::lean_dec_ref(v_a_4442_);
    crate::leanh::lean_dec(v_a_4441_);
    crate::leanh::lean_dec_ref(v_a_4440_);
    crate::leanh::lean_dec(v_a_4439_);
    crate::leanh::lean_dec_ref(v_a_4438_);
    return v_res_4445_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1(
    mut v_cls_4446_: *mut crate::leanh::LeanObject,
    mut v_msg_4447_: *mut crate::leanh::LeanObject,
    mut v___y_4448_: *mut crate::leanh::LeanObject,
    mut v___y_4449_: *mut crate::leanh::LeanObject,
    mut v___y_4450_: *mut crate::leanh::LeanObject,
    mut v___y_4451_: *mut crate::leanh::LeanObject,
    mut v___y_4452_: *mut crate::leanh::LeanObject,
    mut v___y_4453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4455_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___redArg(v_cls_4446_, v_msg_4447_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
    return v___x_4455_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1___boxed(
    mut v_cls_4456_: *mut crate::leanh::LeanObject,
    mut v_msg_4457_: *mut crate::leanh::LeanObject,
    mut v___y_4458_: *mut crate::leanh::LeanObject,
    mut v___y_4459_: *mut crate::leanh::LeanObject,
    mut v___y_4460_: *mut crate::leanh::LeanObject,
    mut v___y_4461_: *mut crate::leanh::LeanObject,
    mut v___y_4462_: *mut crate::leanh::LeanObject,
    mut v___y_4463_: *mut crate::leanh::LeanObject,
    mut v___y_4464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4465_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds_spec__1(v_cls_4456_, v_msg_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
    crate::leanh::lean_dec(v___y_4463_);
    crate::leanh::lean_dec_ref(v___y_4462_);
    crate::leanh::lean_dec(v___y_4461_);
    crate::leanh::lean_dec_ref(v___y_4460_);
    crate::leanh::lean_dec(v___y_4459_);
    crate::leanh::lean_dec_ref(v___y_4458_);
    return v_res_4465_;
}
pub unsafe fn l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg(
    mut v_declName_4466_: *mut crate::leanh::LeanObject,
    mut v___y_4467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: u8 = 0;
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4469_ = lean_st_ref_get(v___y_4467_);
    v_env_4470_ = crate::leanh::lean_ctor_get(v___x_4469_, 0);
    crate::leanh::lean_inc_ref(v_env_4470_);
    crate::leanh::lean_dec(v___x_4469_);
    v___x_4471_ = l_Lean_isInductiveCore(v_env_4470_, v_declName_4466_);
    v___x_4472_ = crate::leanh::lean_box((v___x_4471_) as usize);
    v___x_4473_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4473_, 0, v___x_4472_);
    return v___x_4473_;
}
pub unsafe fn l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg___boxed(
    mut v_declName_4474_: *mut crate::leanh::LeanObject,
    mut v___y_4475_: *mut crate::leanh::LeanObject,
    mut v___y_4476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4477_ =
        l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg(
            v_declName_4474_,
            v___y_4475_,
        );
    crate::leanh::lean_dec(v___y_4475_);
    return v_res_4477_;
}
pub unsafe fn l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0(
    mut v_declName_4478_: *mut crate::leanh::LeanObject,
    mut v___y_4479_: *mut crate::leanh::LeanObject,
    mut v___y_4480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4482_ =
        l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg(
            v_declName_4478_,
            v___y_4480_,
        );
    return v___x_4482_;
}
pub unsafe fn l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___boxed(
    mut v_declName_4483_: *mut crate::leanh::LeanObject,
    mut v___y_4484_: *mut crate::leanh::LeanObject,
    mut v___y_4485_: *mut crate::leanh::LeanObject,
    mut v___y_4486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4487_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0(
        v_declName_4483_,
        v___y_4484_,
        v___y_4485_,
    );
    crate::leanh::lean_dec(v___y_4485_);
    crate::leanh::lean_dec_ref(v___y_4484_);
    return v_res_4487_;
}
pub unsafe fn l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__0(
    mut v_____do__lift_4488_: u8,
    mut v___y_4489_: *mut crate::leanh::LeanObject,
    mut v___y_4490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_4488_ == 0 {
        let mut v___x_4492_: u8 = 0;
        let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4492_ = 1;
        v___x_4493_ = crate::leanh::lean_box((v___x_4492_) as usize);
        v___x_4494_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4494_, 0, v___x_4493_);
        return v___x_4494_;
    } else {
        let mut v___x_4495_: u8 = 0;
        let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4495_ = 0;
        v___x_4496_ = crate::leanh::lean_box((v___x_4495_) as usize);
        v___x_4497_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4497_, 0, v___x_4496_);
        return v___x_4497_;
    }
}
pub unsafe fn l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__0___boxed(
    mut v_____do__lift_4498_: *mut crate::leanh::LeanObject,
    mut v___y_4499_: *mut crate::leanh::LeanObject,
    mut v___y_4500_: *mut crate::leanh::LeanObject,
    mut v___y_4501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_3718__boxed_4502_: u8 = 0;
    let mut v_res_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_3718__boxed_4502_ = (crate::leanh::lean_unbox(v_____do__lift_4498_) as u8);
    v_res_4503_ = l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__0(
        v_____do__lift_3718__boxed_4502_,
        v___y_4499_,
        v___y_4500_,
    );
    crate::leanh::lean_dec(v___y_4500_);
    crate::leanh::lean_dec_ref(v___y_4499_);
    return v_res_4503_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3(
    mut v_as_4504_: *mut crate::leanh::LeanObject,
    mut v_i_4505_: usize,
    mut v_stop_4506_: usize,
    mut v___y_4507_: *mut crate::leanh::LeanObject,
    mut v___y_4508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4510_: u8 = 0;
    let mut v___x_4511_: u8 = 0;
    let mut v_a_4513_: u8 = 0;
    let mut v___x_4514_: usize = 0;
    let mut v___x_4515_: usize = 0;
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4524_: u8 = 0;
    let mut v___x_4525_: u8 = 0;
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4530_: u8 = 0;
    let mut v_a_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: u8 = 0;
    let mut v___x_4533_: u8 = 0;
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4510_ = lean_usize_dec_eq(v_i_4505_, v_stop_4506_);
                if v___x_4510_ == 0 {
                    v___x_4511_ = 1;
                    v___x_4519_ = lean_array_uget_borrowed(v_as_4504_, v_i_4505_);
                    crate::leanh::lean_inc(v___x_4519_);
                    v___x_4520_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__0___redArg(v___x_4519_, v___y_4508_);
                    if crate::leanh::lean_obj_tag(v___x_4520_) == 0 {
                        v_a_4521_ = crate::leanh::lean_ctor_get(v___x_4520_, 0);
                        v_isSharedCheck_4530_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4520_)) as u8;
                        if v_isSharedCheck_4530_ == 0 {
                            v___x_4523_ = v___x_4520_;
                            v_isShared_4524_ = v_isSharedCheck_4530_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4521_);
                            crate::leanh::lean_dec(v___x_4520_);
                            v___x_4523_ = crate::leanh::lean_box(0);
                            v_isShared_4524_ = v_isSharedCheck_4530_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_4520_) == 0 {
                            v_a_4531_ = crate::leanh::lean_ctor_get(v___x_4520_, 0);
                            crate::leanh::lean_inc(v_a_4531_);
                            crate::leanh::lean_dec_ref_known(v___x_4520_, 1);
                            v___x_4532_ = (crate::leanh::lean_unbox(v_a_4531_) as u8);
                            crate::leanh::lean_dec(v_a_4531_);
                            v_a_4513_ = v___x_4532_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_4520_;
                        }
                    }
                } else {
                    v___x_4533_ = 0;
                    v___x_4534_ = crate::leanh::lean_box((v___x_4533_) as usize);
                    v___x_4535_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4535_, 0, v___x_4534_);
                    return v___x_4535_;
                }
            }
            1 => {
                if v_a_4513_ == 0 {
                    v___x_4514_ = 1usize;
                    v___x_4515_ = lean_usize_add(v_i_4505_, v___x_4514_);
                    v_i_4505_ = v___x_4515_;
                    state = 0;
                    continue;
                } else {
                    v___x_4517_ = crate::leanh::lean_box((v___x_4511_) as usize);
                    v___x_4518_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4518_, 0, v___x_4517_);
                    return v___x_4518_;
                }
            }
            2 => {
                v___x_4525_ = (crate::leanh::lean_unbox(v_a_4521_) as u8);
                crate::leanh::lean_dec(v_a_4521_);
                if v___x_4525_ == 0 {
                    v___x_4526_ = crate::leanh::lean_box((v___x_4511_) as usize);
                    if v_isShared_4524_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4523_, 0, v___x_4526_);
                        v___x_4528_ = v___x_4523_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4529_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4529_, 0, v___x_4526_);
                        v___x_4528_ = v_reuseFailAlloc_4529_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4523_);
                    v_a_4513_ = v___x_4510_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_4528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3___boxed(
    mut v_as_4536_: *mut crate::leanh::LeanObject,
    mut v_i_4537_: *mut crate::leanh::LeanObject,
    mut v_stop_4538_: *mut crate::leanh::LeanObject,
    mut v___y_4539_: *mut crate::leanh::LeanObject,
    mut v___y_4540_: *mut crate::leanh::LeanObject,
    mut v___y_4541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4542_: usize = 0;
    let mut v_stop_boxed_4543_: usize = 0;
    let mut v_res_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4542_ = crate::leanh::lean_unbox_usize(v_i_4537_);
    crate::leanh::lean_dec(v_i_4537_);
    v_stop_boxed_4543_ = crate::leanh::lean_unbox_usize(v_stop_4538_);
    crate::leanh::lean_dec(v_stop_4538_);
    v_res_4544_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3(v_as_4536_, v_i_boxed_4542_, v_stop_boxed_4543_, v___y_4539_, v___y_4540_);
    crate::leanh::lean_dec(v___y_4540_);
    crate::leanh::lean_dec_ref(v___y_4539_);
    crate::leanh::lean_dec_ref(v_as_4536_);
    return v_res_4544_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1(
    mut v_as_4545_: *mut crate::leanh::LeanObject,
    mut v_i_4546_: usize,
    mut v_stop_4547_: usize,
    mut v_b_4548_: *mut crate::leanh::LeanObject,
    mut v___y_4549_: *mut crate::leanh::LeanObject,
    mut v___y_4550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4552_: u8 = 0;
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: usize = 0;
    let mut v___x_4557_: usize = 0;
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4552_ = lean_usize_dec_eq(v_i_4546_, v_stop_4547_);
                if v___x_4552_ == 0 {
                    v___x_4553_ = lean_array_uget_borrowed(v_as_4545_, v_i_4546_);
                    crate::leanh::lean_inc(v___x_4553_);
                    v___x_4554_ =
                        l_Lean_Elab_Command_elabCommand(v___x_4553_, v___y_4549_, v___y_4550_);
                    if crate::leanh::lean_obj_tag(v___x_4554_) == 0 {
                        v_a_4555_ = crate::leanh::lean_ctor_get(v___x_4554_, 0);
                        crate::leanh::lean_inc(v_a_4555_);
                        crate::leanh::lean_dec_ref_known(v___x_4554_, 1);
                        v___x_4556_ = 1usize;
                        v___x_4557_ = lean_usize_add(v_i_4546_, v___x_4556_);
                        v_i_4546_ = v___x_4557_;
                        v_b_4548_ = v_a_4555_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4554_;
                    }
                } else {
                    v___x_4559_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4559_, 0, v_b_4548_);
                    return v___x_4559_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1___boxed(
    mut v_as_4560_: *mut crate::leanh::LeanObject,
    mut v_i_4561_: *mut crate::leanh::LeanObject,
    mut v_stop_4562_: *mut crate::leanh::LeanObject,
    mut v_b_4563_: *mut crate::leanh::LeanObject,
    mut v___y_4564_: *mut crate::leanh::LeanObject,
    mut v___y_4565_: *mut crate::leanh::LeanObject,
    mut v___y_4566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4567_: usize = 0;
    let mut v_stop_boxed_4568_: usize = 0;
    let mut v_res_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4567_ = crate::leanh::lean_unbox_usize(v_i_4561_);
    crate::leanh::lean_dec(v_i_4561_);
    v_stop_boxed_4568_ = crate::leanh::lean_unbox_usize(v_stop_4562_);
    crate::leanh::lean_dec(v_stop_4562_);
    v_res_4569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1(v_as_4560_, v_i_boxed_4567_, v_stop_boxed_4568_, v_b_4563_, v___y_4564_, v___y_4565_);
    crate::leanh::lean_dec(v___y_4565_);
    crate::leanh::lean_dec_ref(v___y_4564_);
    crate::leanh::lean_dec_ref(v_as_4560_);
    return v_res_4569_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0(
    mut v___x_4570_: *mut crate::leanh::LeanObject,
    mut v___x_4571_: *mut crate::leanh::LeanObject,
    mut v___x_4572_: *mut crate::leanh::LeanObject,
    mut v___y_4573_: *mut crate::leanh::LeanObject,
    mut v___y_4574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4580_: u8 = 0;
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: u8 = 0;
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: u8 = 0;
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: usize = 0;
    let mut v___x_4591_: usize = 0;
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: usize = 0;
    let mut v___x_4594_: usize = 0;
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4596_: u8 = 0;
    let mut v_a_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4600_: u8 = 0;
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4604_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4576_ = l_Lean_Elab_Command_liftTermElabM___redArg(
                    v___x_4570_,
                    v___y_4573_,
                    v___y_4574_,
                );
                if crate::leanh::lean_obj_tag(v___x_4576_) == 0 {
                    v_a_4577_ = crate::leanh::lean_ctor_get(v___x_4576_, 0);
                    v_isSharedCheck_4596_ = (!crate::leanh::lean_is_exclusive(v___x_4576_)) as u8;
                    if v_isSharedCheck_4596_ == 0 {
                        v___x_4579_ = v___x_4576_;
                        v_isShared_4580_ = v_isSharedCheck_4596_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4577_);
                        crate::leanh::lean_dec(v___x_4576_);
                        v___x_4579_ = crate::leanh::lean_box(0);
                        v_isShared_4580_ = v_isSharedCheck_4596_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4597_ = crate::leanh::lean_ctor_get(v___x_4576_, 0);
                    v_isSharedCheck_4604_ = (!crate::leanh::lean_is_exclusive(v___x_4576_)) as u8;
                    if v_isSharedCheck_4604_ == 0 {
                        v___x_4599_ = v___x_4576_;
                        v_isShared_4600_ = v_isSharedCheck_4604_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4597_);
                        crate::leanh::lean_dec(v___x_4576_);
                        v___x_4599_ = crate::leanh::lean_box(0);
                        v_isShared_4600_ = v_isSharedCheck_4604_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4581_ = lean_array_get_size(v_a_4577_);
                v___x_4582_ = lean_nat_dec_lt(v___x_4571_, v___x_4581_);
                if v___x_4582_ == 0 {
                    crate::leanh::lean_dec(v_a_4577_);
                    if v_isShared_4580_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4579_, 0, v___x_4572_);
                        v___x_4584_ = v___x_4579_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4585_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 0, v___x_4572_);
                        v___x_4584_ = v_reuseFailAlloc_4585_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4586_ = lean_nat_dec_le(v___x_4581_, v___x_4581_);
                    if v___x_4586_ == 0 {
                        if v___x_4582_ == 0 {
                            crate::leanh::lean_dec(v_a_4577_);
                            if v_isShared_4580_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4579_, 0, v___x_4572_);
                                v___x_4588_ = v___x_4579_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_4589_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4589_, 0, v___x_4572_);
                                v___x_4588_ = v_reuseFailAlloc_4589_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4579_);
                            v___x_4590_ = 0usize;
                            v___x_4591_ = lean_usize_of_nat(v___x_4581_);
                            v___x_4592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1(v_a_4577_, v___x_4590_, v___x_4591_, v___x_4572_, v___y_4573_, v___y_4574_);
                            crate::leanh::lean_dec(v_a_4577_);
                            return v___x_4592_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4579_);
                        v___x_4593_ = 0usize;
                        v___x_4594_ = lean_usize_of_nat(v___x_4581_);
                        v___x_4595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__1(v_a_4577_, v___x_4593_, v___x_4594_, v___x_4572_, v___y_4573_, v___y_4574_);
                        crate::leanh::lean_dec(v_a_4577_);
                        return v___x_4595_;
                    }
                }
            }
            2 => {
                return v___x_4584_;
            }
            3 => {
                return v___x_4588_;
            }
            4 => {
                if v_isShared_4600_ == 0 {
                    v___x_4602_ = v___x_4599_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4603_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_a_4597_);
                    v___x_4602_ = v_reuseFailAlloc_4603_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4602_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0___boxed(
    mut v___x_4605_: *mut crate::leanh::LeanObject,
    mut v___x_4606_: *mut crate::leanh::LeanObject,
    mut v___x_4607_: *mut crate::leanh::LeanObject,
    mut v___y_4608_: *mut crate::leanh::LeanObject,
    mut v___y_4609_: *mut crate::leanh::LeanObject,
    mut v___y_4610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0(v___x_4605_, v___x_4606_, v___x_4607_, v___y_4608_, v___y_4609_);
    crate::leanh::lean_dec(v___y_4609_);
    crate::leanh::lean_dec_ref(v___y_4608_);
    crate::leanh::lean_dec(v___x_4606_);
    return v_res_4611_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2(
    mut v_as_4612_: *mut crate::leanh::LeanObject,
    mut v_sz_4613_: usize,
    mut v_i_4614_: usize,
    mut v_b_4615_: *mut crate::leanh::LeanObject,
    mut v___y_4616_: *mut crate::leanh::LeanObject,
    mut v___y_4617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4619_: u8 = 0;
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: usize = 0;
    let mut v___x_4628_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4619_ = lean_usize_dec_lt(v_i_4614_, v_sz_4613_);
                if v___x_4619_ == 0 {
                    v___x_4620_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4620_, 0, v_b_4615_);
                    return v___x_4620_;
                } else {
                    v___x_4621_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4622_ = crate::leanh::lean_box(0);
                    v_a_4623_ = lean_array_uget_borrowed(v_as_4612_, v_i_4614_);
                    crate::leanh::lean_inc_n(v_a_4623_, 2);
                    v___x_4624_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___boxed as *mut core::ffi::c_void, 8, 1);
                    crate::leanh::lean_closure_set(v___x_4624_, 0, v_a_4623_);
                    v___f_4625_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___lam__0___boxed as *mut core::ffi::c_void, 6, 3);
                    crate::leanh::lean_closure_set(v___f_4625_, 0, v___x_4624_);
                    crate::leanh::lean_closure_set(v___f_4625_, 1, v___x_4621_);
                    crate::leanh::lean_closure_set(v___f_4625_, 2, v___x_4622_);
                    v___x_4626_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(
                        v_a_4623_,
                        v___f_4625_,
                        v___y_4616_,
                        v___y_4617_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4626_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4626_, 1);
                        v___x_4627_ = 1usize;
                        v___x_4628_ = lean_usize_add(v_i_4614_, v___x_4627_);
                        v_i_4614_ = v___x_4628_;
                        v_b_4615_ = v___x_4622_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4626_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2___boxed(
    mut v_as_4630_: *mut crate::leanh::LeanObject,
    mut v_sz_4631_: *mut crate::leanh::LeanObject,
    mut v_i_4632_: *mut crate::leanh::LeanObject,
    mut v_b_4633_: *mut crate::leanh::LeanObject,
    mut v___y_4634_: *mut crate::leanh::LeanObject,
    mut v___y_4635_: *mut crate::leanh::LeanObject,
    mut v___y_4636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4637_: usize = 0;
    let mut v_i_boxed_4638_: usize = 0;
    let mut v_res_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4637_ = crate::leanh::lean_unbox_usize(v_sz_4631_);
    crate::leanh::lean_dec(v_sz_4631_);
    v_i_boxed_4638_ = crate::leanh::lean_unbox_usize(v_i_4632_);
    crate::leanh::lean_dec(v_i_4632_);
    v_res_4639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2(v_as_4630_, v_sz_boxed_4637_, v_i_boxed_4638_, v_b_4633_, v___y_4634_, v___y_4635_);
    crate::leanh::lean_dec(v___y_4635_);
    crate::leanh::lean_dec_ref(v___y_4634_);
    crate::leanh::lean_dec_ref(v_as_4630_);
    return v_res_4639_;
}
pub unsafe fn l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1(
    mut v_declNames_4640_: *mut crate::leanh::LeanObject,
    mut v___x_4641_: *mut crate::leanh::LeanObject,
    mut v___x_4642_: *mut crate::leanh::LeanObject,
    mut v___f_4643_: *mut crate::leanh::LeanObject,
    mut v___y_4644_: *mut crate::leanh::LeanObject,
    mut v___y_4645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4649_: usize = 0;
    let mut v___x_4650_: usize = 0;
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4654_: u8 = 0;
    let mut v___x_4655_: u8 = 0;
    let mut v___x_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4660_: u8 = 0;
    let mut v_unused_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4665_: u8 = 0;
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4669_: u8 = 0;
    let mut v___y_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: u8 = 0;
    let mut v___x_4674_: u8 = 0;
    let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: usize = 0;
    let mut v___x_4678_: usize = 0;
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4674_ = lean_nat_dec_lt(v___x_4641_, v___x_4642_);
                if v___x_4674_ == 0 {
                    v___x_4675_ = crate::leanh::lean_box((v___x_4674_) as usize);
                    crate::leanh::lean_inc(v___y_4645_);
                    crate::leanh::lean_inc_ref(v___y_4644_);
                    v___x_4676_ = crate::leanh::lean_apply_4(
                        v___f_4643_,
                        v___x_4675_,
                        v___y_4644_,
                        v___y_4645_,
                        crate::leanh::lean_box(0),
                    );
                    v___y_4671_ = v___x_4676_;
                    state = 6;
                    continue;
                } else {
                    if v___x_4674_ == 0 {
                        crate::leanh::lean_dec_ref(v___f_4643_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4677_ = 0usize;
                        v___x_4678_ = lean_usize_of_nat(v___x_4642_);
                        v___x_4679_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__3(v_declNames_4640_, v___x_4677_, v___x_4678_, v___y_4644_, v___y_4645_);
                        if crate::leanh::lean_obj_tag(v___x_4679_) == 0 {
                            v_a_4680_ = crate::leanh::lean_ctor_get(v___x_4679_, 0);
                            crate::leanh::lean_inc(v_a_4680_);
                            crate::leanh::lean_dec_ref_known(v___x_4679_, 1);
                            crate::leanh::lean_inc(v___y_4645_);
                            crate::leanh::lean_inc_ref(v___y_4644_);
                            v___x_4681_ = crate::leanh::lean_apply_4(
                                v___f_4643_,
                                v_a_4680_,
                                v___y_4644_,
                                v___y_4645_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_4671_ = v___x_4681_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___f_4643_);
                            v___y_4671_ = v___x_4679_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4648_ = crate::leanh::lean_box(0);
                v_sz_4649_ = lean_array_size(v_declNames_4640_);
                v___x_4650_ = 0usize;
                v___x_4651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__2(v_declNames_4640_, v_sz_4649_, v___x_4650_, v___x_4648_, v___y_4644_, v___y_4645_);
                crate::leanh::lean_dec(v___y_4645_);
                crate::leanh::lean_dec_ref(v___y_4644_);
                if crate::leanh::lean_obj_tag(v___x_4651_) == 0 {
                    v_isSharedCheck_4660_ = (!crate::leanh::lean_is_exclusive(v___x_4651_)) as u8;
                    if v_isSharedCheck_4660_ == 0 {
                        v_unused_4661_ = crate::leanh::lean_ctor_get(v___x_4651_, 0);
                        crate::leanh::lean_dec(v_unused_4661_);
                        v___x_4653_ = v___x_4651_;
                        v_isShared_4654_ = v_isSharedCheck_4660_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4651_);
                        v___x_4653_ = crate::leanh::lean_box(0);
                        v_isShared_4654_ = v_isSharedCheck_4660_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4662_ = crate::leanh::lean_ctor_get(v___x_4651_, 0);
                    v_isSharedCheck_4669_ = (!crate::leanh::lean_is_exclusive(v___x_4651_)) as u8;
                    if v_isSharedCheck_4669_ == 0 {
                        v___x_4664_ = v___x_4651_;
                        v_isShared_4665_ = v_isSharedCheck_4669_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4662_);
                        crate::leanh::lean_dec(v___x_4651_);
                        v___x_4664_ = crate::leanh::lean_box(0);
                        v_isShared_4665_ = v_isSharedCheck_4669_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4655_ = 1;
                v___x_4656_ = crate::leanh::lean_box((v___x_4655_) as usize);
                if v_isShared_4654_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4653_, 0, v___x_4656_);
                    v___x_4658_ = v___x_4653_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4659_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4659_, 0, v___x_4656_);
                    v___x_4658_ = v_reuseFailAlloc_4659_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4658_;
            }
            4 => {
                if v_isShared_4665_ == 0 {
                    v___x_4667_ = v___x_4664_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4668_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4668_, 0, v_a_4662_);
                    v___x_4667_ = v_reuseFailAlloc_4668_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4667_;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v___y_4671_) == 0 {
                    v_a_4672_ = crate::leanh::lean_ctor_get(v___y_4671_, 0);
                    v___x_4673_ = (crate::leanh::lean_unbox(v_a_4672_) as u8);
                    if v___x_4673_ == 0 {
                        crate::leanh::lean_dec(v___y_4645_);
                        crate::leanh::lean_dec_ref(v___y_4644_);
                        return v___y_4671_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_4671_, 1);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_4645_);
                    crate::leanh::lean_dec_ref(v___y_4644_);
                    return v___y_4671_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1___boxed(
    mut v_declNames_4682_: *mut crate::leanh::LeanObject,
    mut v___x_4683_: *mut crate::leanh::LeanObject,
    mut v___x_4684_: *mut crate::leanh::LeanObject,
    mut v___f_4685_: *mut crate::leanh::LeanObject,
    mut v___y_4686_: *mut crate::leanh::LeanObject,
    mut v___y_4687_: *mut crate::leanh::LeanObject,
    mut v___y_4688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4689_ = l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1(
        v_declNames_4682_,
        v___x_4683_,
        v___x_4684_,
        v___f_4685_,
        v___y_4686_,
        v___y_4687_,
    );
    crate::leanh::lean_dec(v___x_4684_);
    crate::leanh::lean_dec(v___x_4683_);
    crate::leanh::lean_dec_ref(v_declNames_4682_);
    return v_res_4689_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0(
    mut v___y_4690_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4691_: u8,
    mut v_a_x3f_4692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4708_: u8 = 0;
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4716_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4694_ = lean_st_ref_take(v___y_4690_);
                v_env_4695_ = crate::leanh::lean_ctor_get(v___x_4694_, 0);
                v_messages_4696_ = crate::leanh::lean_ctor_get(v___x_4694_, 1);
                v_scopes_4697_ = crate::leanh::lean_ctor_get(v___x_4694_, 2);
                v_usedQuotCtxts_4698_ = crate::leanh::lean_ctor_get(v___x_4694_, 3);
                v_nextMacroScope_4699_ = crate::leanh::lean_ctor_get(v___x_4694_, 4);
                v_maxRecDepth_4700_ = crate::leanh::lean_ctor_get(v___x_4694_, 5);
                v_ngen_4701_ = crate::leanh::lean_ctor_get(v___x_4694_, 6);
                v_auxDeclNGen_4702_ = crate::leanh::lean_ctor_get(v___x_4694_, 7);
                v_infoState_4703_ = crate::leanh::lean_ctor_get(v___x_4694_, 8);
                v_traceState_4704_ = crate::leanh::lean_ctor_get(v___x_4694_, 9);
                v_snapshotTasks_4705_ = crate::leanh::lean_ctor_get(v___x_4694_, 10);
                v_isSharedCheck_4716_ = (!crate::leanh::lean_is_exclusive(v___x_4694_)) as u8;
                if v_isSharedCheck_4716_ == 0 {
                    v___x_4707_ = v___x_4694_;
                    v_isShared_4708_ = v_isSharedCheck_4716_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4705_);
                    crate::leanh::lean_inc(v_traceState_4704_);
                    crate::leanh::lean_inc(v_infoState_4703_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4702_);
                    crate::leanh::lean_inc(v_ngen_4701_);
                    crate::leanh::lean_inc(v_maxRecDepth_4700_);
                    crate::leanh::lean_inc(v_nextMacroScope_4699_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_4698_);
                    crate::leanh::lean_inc(v_scopes_4697_);
                    crate::leanh::lean_inc(v_messages_4696_);
                    crate::leanh::lean_inc(v_env_4695_);
                    crate::leanh::lean_dec(v___x_4694_);
                    v___x_4707_ = crate::leanh::lean_box(0);
                    v_isShared_4708_ = v_isSharedCheck_4716_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4709_ = l_Lean_Environment_setExporting(v_env_4695_, v_isExporting_4691_);
                if v_isShared_4708_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4707_, 0, v___x_4709_);
                    v___x_4711_ = v___x_4707_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4715_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4715_, 0, v___x_4709_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4715_, 1, v_messages_4696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4715_, 2, v_scopes_4697_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4715_, 3, v_usedQuotCtxts_4698_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4715_, 4, v_nextMacroScope_4699_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4715_, 5, v_maxRecDepth_4700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4715_, 6, v_ngen_4701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4715_, 7, v_auxDeclNGen_4702_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4715_, 8, v_infoState_4703_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4715_, 9, v_traceState_4704_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4715_, 10, v_snapshotTasks_4705_);
                    v___x_4711_ = v_reuseFailAlloc_4715_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4712_ = lean_st_ref_set(v___y_4690_, v___x_4711_);
                v___x_4713_ = crate::leanh::lean_box(0);
                v___x_4714_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4714_, 0, v___x_4713_);
                return v___x_4714_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0___boxed(
    mut v___y_4717_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4718_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_4719_: *mut crate::leanh::LeanObject,
    mut v___y_4720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_4721_: u8 = 0;
    let mut v_res_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4721_ = (crate::leanh::lean_unbox(v_isExporting_4718_) as u8);
    v_res_4722_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0(v___y_4717_, v_isExporting_boxed_4721_, v_a_x3f_4719_);
    crate::leanh::lean_dec(v_a_x3f_4719_);
    crate::leanh::lean_dec(v___y_4717_);
    return v_res_4722_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg(
    mut v_x_4723_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4724_: u8,
    mut v___y_4725_: *mut crate::leanh::LeanObject,
    mut v___y_4726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4730_: u8 = 0;
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4745_: u8 = 0;
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4754_: u8 = 0;
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4760_: u8 = 0;
    let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4764_: u8 = 0;
    let mut v_unused_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4767_: u8 = 0;
    let mut v_a_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4773_: u8 = 0;
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4777_: u8 = 0;
    let mut v_unused_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4780_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4728_ = lean_st_ref_get(v___y_4726_);
                v_env_4729_ = crate::leanh::lean_ctor_get(v___x_4728_, 0);
                crate::leanh::lean_inc_ref(v_env_4729_);
                crate::leanh::lean_dec(v___x_4728_);
                v_isExporting_4730_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_4729_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_4729_);
                v___x_4731_ = lean_st_ref_take(v___y_4726_);
                v_env_4732_ = crate::leanh::lean_ctor_get(v___x_4731_, 0);
                v_messages_4733_ = crate::leanh::lean_ctor_get(v___x_4731_, 1);
                v_scopes_4734_ = crate::leanh::lean_ctor_get(v___x_4731_, 2);
                v_usedQuotCtxts_4735_ = crate::leanh::lean_ctor_get(v___x_4731_, 3);
                v_nextMacroScope_4736_ = crate::leanh::lean_ctor_get(v___x_4731_, 4);
                v_maxRecDepth_4737_ = crate::leanh::lean_ctor_get(v___x_4731_, 5);
                v_ngen_4738_ = crate::leanh::lean_ctor_get(v___x_4731_, 6);
                v_auxDeclNGen_4739_ = crate::leanh::lean_ctor_get(v___x_4731_, 7);
                v_infoState_4740_ = crate::leanh::lean_ctor_get(v___x_4731_, 8);
                v_traceState_4741_ = crate::leanh::lean_ctor_get(v___x_4731_, 9);
                v_snapshotTasks_4742_ = crate::leanh::lean_ctor_get(v___x_4731_, 10);
                v_isSharedCheck_4780_ = (!crate::leanh::lean_is_exclusive(v___x_4731_)) as u8;
                if v_isSharedCheck_4780_ == 0 {
                    v___x_4744_ = v___x_4731_;
                    v_isShared_4745_ = v_isSharedCheck_4780_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4742_);
                    crate::leanh::lean_inc(v_traceState_4741_);
                    crate::leanh::lean_inc(v_infoState_4740_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4739_);
                    crate::leanh::lean_inc(v_ngen_4738_);
                    crate::leanh::lean_inc(v_maxRecDepth_4737_);
                    crate::leanh::lean_inc(v_nextMacroScope_4736_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_4735_);
                    crate::leanh::lean_inc(v_scopes_4734_);
                    crate::leanh::lean_inc(v_messages_4733_);
                    crate::leanh::lean_inc(v_env_4732_);
                    crate::leanh::lean_dec(v___x_4731_);
                    v___x_4744_ = crate::leanh::lean_box(0);
                    v_isShared_4745_ = v_isSharedCheck_4780_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4746_ = l_Lean_Environment_setExporting(v_env_4732_, v_isExporting_4724_);
                if v_isShared_4745_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4744_, 0, v___x_4746_);
                    v___x_4748_ = v___x_4744_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4779_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 0, v___x_4746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 1, v_messages_4733_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 2, v_scopes_4734_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 3, v_usedQuotCtxts_4735_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 4, v_nextMacroScope_4736_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 5, v_maxRecDepth_4737_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 6, v_ngen_4738_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 7, v_auxDeclNGen_4739_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 8, v_infoState_4740_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 9, v_traceState_4741_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 10, v_snapshotTasks_4742_);
                    v___x_4748_ = v_reuseFailAlloc_4779_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4749_ = lean_st_ref_set(v___y_4726_, v___x_4748_);
                crate::leanh::lean_inc(v___y_4726_);
                crate::leanh::lean_inc_ref(v___y_4725_);
                v_r_4750_ = crate::leanh::lean_apply_3(
                    v_x_4723_,
                    v___y_4725_,
                    v___y_4726_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v_r_4750_) == 0 {
                    v_a_4751_ = crate::leanh::lean_ctor_get(v_r_4750_, 0);
                    v_isSharedCheck_4767_ = (!crate::leanh::lean_is_exclusive(v_r_4750_)) as u8;
                    if v_isSharedCheck_4767_ == 0 {
                        v___x_4753_ = v_r_4750_;
                        v_isShared_4754_ = v_isSharedCheck_4767_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4751_);
                        crate::leanh::lean_dec(v_r_4750_);
                        v___x_4753_ = crate::leanh::lean_box(0);
                        v_isShared_4754_ = v_isSharedCheck_4767_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_4768_ = crate::leanh::lean_ctor_get(v_r_4750_, 0);
                    crate::leanh::lean_inc(v_a_4768_);
                    crate::leanh::lean_dec_ref_known(v_r_4750_, 1);
                    v___x_4769_ = crate::leanh::lean_box(0);
                    v___x_4770_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0(v___y_4726_, v_isExporting_4730_, v___x_4769_);
                    v_isSharedCheck_4777_ = (!crate::leanh::lean_is_exclusive(v___x_4770_)) as u8;
                    if v_isSharedCheck_4777_ == 0 {
                        v_unused_4778_ = crate::leanh::lean_ctor_get(v___x_4770_, 0);
                        crate::leanh::lean_dec(v_unused_4778_);
                        v___x_4772_ = v___x_4770_;
                        v_isShared_4773_ = v_isSharedCheck_4777_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4770_);
                        v___x_4772_ = crate::leanh::lean_box(0);
                        v_isShared_4773_ = v_isSharedCheck_4777_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc(v_a_4751_);
                if v_isShared_4754_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4753_, 1);
                    v___x_4756_ = v___x_4753_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4766_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_a_4751_);
                    v___x_4756_ = v_reuseFailAlloc_4766_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4757_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___lam__0(v___y_4726_, v_isExporting_4730_, v___x_4756_);
                crate::leanh::lean_dec_ref(v___x_4756_);
                v_isSharedCheck_4764_ = (!crate::leanh::lean_is_exclusive(v___x_4757_)) as u8;
                if v_isSharedCheck_4764_ == 0 {
                    v_unused_4765_ = crate::leanh::lean_ctor_get(v___x_4757_, 0);
                    crate::leanh::lean_dec(v_unused_4765_);
                    v___x_4759_ = v___x_4757_;
                    v_isShared_4760_ = v_isSharedCheck_4764_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4757_);
                    v___x_4759_ = crate::leanh::lean_box(0);
                    v_isShared_4760_ = v_isSharedCheck_4764_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4760_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4759_, 0, v_a_4751_);
                    v___x_4762_ = v___x_4759_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4763_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4763_, 0, v_a_4751_);
                    v___x_4762_ = v_reuseFailAlloc_4763_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4762_;
            }
            7 => {
                if v_isShared_4773_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4772_, 1);
                    crate::leanh::lean_ctor_set(v___x_4772_, 0, v_a_4768_);
                    v___x_4775_ = v___x_4772_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4776_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4776_, 0, v_a_4768_);
                    v___x_4775_ = v_reuseFailAlloc_4776_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4775_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg___boxed(
    mut v_x_4781_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4782_: *mut crate::leanh::LeanObject,
    mut v___y_4783_: *mut crate::leanh::LeanObject,
    mut v___y_4784_: *mut crate::leanh::LeanObject,
    mut v___y_4785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_4786_: u8 = 0;
    let mut v_res_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4786_ = (crate::leanh::lean_unbox(v_isExporting_4782_) as u8);
    v_res_4787_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg(v_x_4781_, v_isExporting_boxed_4786_, v___y_4783_, v___y_4784_);
    crate::leanh::lean_dec(v___y_4784_);
    crate::leanh::lean_dec_ref(v___y_4783_);
    return v_res_4787_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg(
    mut v_x_4788_: *mut crate::leanh::LeanObject,
    mut v_when_4789_: u8,
    mut v___y_4790_: *mut crate::leanh::LeanObject,
    mut v___y_4791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_when_4789_ == 0 {
        let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v___y_4791_);
        crate::leanh::lean_inc_ref(v___y_4790_);
        v___x_4793_ = crate::leanh::lean_apply_3(
            v_x_4788_,
            v___y_4790_,
            v___y_4791_,
            crate::leanh::lean_box(0),
        );
        return v___x_4793_;
    } else {
        let mut v___x_4794_: u8 = 0;
        let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4794_ = 0;
        v___x_4795_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg(v_x_4788_, v___x_4794_, v___y_4790_, v___y_4791_);
        return v___x_4795_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg___boxed(
    mut v_x_4796_: *mut crate::leanh::LeanObject,
    mut v_when_4797_: *mut crate::leanh::LeanObject,
    mut v___y_4798_: *mut crate::leanh::LeanObject,
    mut v___y_4799_: *mut crate::leanh::LeanObject,
    mut v___y_4800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_when_boxed_4801_: u8 = 0;
    let mut v_res_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_4801_ = (crate::leanh::lean_unbox(v_when_4797_) as u8);
    v_res_4802_ = l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg(v_x_4796_, v_when_boxed_4801_, v___y_4798_, v___y_4799_);
    crate::leanh::lean_dec(v___y_4799_);
    crate::leanh::lean_dec_ref(v___y_4798_);
    return v_res_4802_;
}
pub unsafe fn l_Lean_Elab_Deriving_Hashable_mkHashableHandler(
    mut v_declNames_4804_: *mut crate::leanh::LeanObject,
    mut v_a_4805_: *mut crate::leanh::LeanObject,
    mut v_a_4806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: u8 = 0;
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4808_ = l_Lean_Elab_Deriving_Hashable_mkHashableHandler___closed__0;
    v___x_4809_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4810_ = lean_array_get_size(v_declNames_4804_);
    v___f_4811_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Deriving_Hashable_mkHashableHandler___lam__1___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4811_, 0, v_declNames_4804_);
    crate::leanh::lean_closure_set(v___f_4811_, 1, v___x_4809_);
    crate::leanh::lean_closure_set(v___f_4811_, 2, v___x_4810_);
    crate::leanh::lean_closure_set(v___f_4811_, 3, v___f_4808_);
    v___x_4812_ = 1;
    v___x_4813_ = l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg(v___f_4811_, v___x_4812_, v_a_4805_, v_a_4806_);
    return v___x_4813_;
}
pub unsafe fn l_Lean_Elab_Deriving_Hashable_mkHashableHandler___boxed(
    mut v_declNames_4814_: *mut crate::leanh::LeanObject,
    mut v_a_4815_: *mut crate::leanh::LeanObject,
    mut v_a_4816_: *mut crate::leanh::LeanObject,
    mut v_a_4817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4818_ =
        l_Lean_Elab_Deriving_Hashable_mkHashableHandler(v_declNames_4814_, v_a_4815_, v_a_4816_);
    crate::leanh::lean_dec(v_a_4816_);
    crate::leanh::lean_dec_ref(v_a_4815_);
    return v_res_4818_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4(
    mut v_00_u03b1_4819_: *mut crate::leanh::LeanObject,
    mut v_x_4820_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4821_: u8,
    mut v___y_4822_: *mut crate::leanh::LeanObject,
    mut v___y_4823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4825_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___redArg(v_x_4820_, v_isExporting_4821_, v___y_4822_, v___y_4823_);
    return v___x_4825_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4___boxed(
    mut v_00_u03b1_4826_: *mut crate::leanh::LeanObject,
    mut v_x_4827_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4828_: *mut crate::leanh::LeanObject,
    mut v___y_4829_: *mut crate::leanh::LeanObject,
    mut v___y_4830_: *mut crate::leanh::LeanObject,
    mut v___y_4831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_4832_: u8 = 0;
    let mut v_res_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4832_ = (crate::leanh::lean_unbox(v_isExporting_4828_) as u8);
    v_res_4833_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4_spec__4(v_00_u03b1_4826_, v_x_4827_, v_isExporting_boxed_4832_, v___y_4829_, v___y_4830_);
    crate::leanh::lean_dec(v___y_4830_);
    crate::leanh::lean_dec_ref(v___y_4829_);
    return v_res_4833_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4(
    mut v_00_u03b1_4834_: *mut crate::leanh::LeanObject,
    mut v_x_4835_: *mut crate::leanh::LeanObject,
    mut v_when_4836_: u8,
    mut v___y_4837_: *mut crate::leanh::LeanObject,
    mut v___y_4838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4840_ = l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___redArg(v_x_4835_, v_when_4836_, v___y_4837_, v___y_4838_);
    return v___x_4840_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4___boxed(
    mut v_00_u03b1_4841_: *mut crate::leanh::LeanObject,
    mut v_x_4842_: *mut crate::leanh::LeanObject,
    mut v_when_4843_: *mut crate::leanh::LeanObject,
    mut v___y_4844_: *mut crate::leanh::LeanObject,
    mut v___y_4845_: *mut crate::leanh::LeanObject,
    mut v___y_4846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_when_boxed_4847_: u8 = 0;
    let mut v_res_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_4847_ = (crate::leanh::lean_unbox(v_when_4843_) as u8);
    v_res_4848_ =
        l_Lean_withoutExporting___at___00Lean_Elab_Deriving_Hashable_mkHashableHandler_spec__4(
            v_00_u03b1_4841_,
            v_x_4842_,
            v_when_boxed_4847_,
            v___y_4844_,
            v___y_4845_,
        );
    crate::leanh::lean_dec(v___y_4845_);
    crate::leanh::lean_dec_ref(v___y_4844_);
    return v_res_4848_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4901_ = crate::leanh::lean_unsigned_to_nat(4079464183);
    v___x_4902_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__19_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_;
    v___x_4903_ = l_Lean_Name_num___override(v___x_4902_, v___x_4901_);
    return v___x_4903_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4905_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__21_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_;
    v___x_4906_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__20_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_);
    v___x_4907_ = l_Lean_Name_str___override(v___x_4906_, v___x_4905_);
    return v___x_4907_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4909_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__23_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_;
    v___x_4910_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__22_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_);
    v___x_4911_ = l_Lean_Name_str___override(v___x_4910_, v___x_4909_);
    return v___x_4911_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4912_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_4913_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__24_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_);
    v___x_4914_ = l_Lean_Name_num___override(v___x_4913_, v___x_4912_);
    return v___x_4914_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4916_ = l_Lean_Elab_Deriving_Hashable_mkHashableHeader___closed__1;
    v___x_4917_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__0_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_;
    v___x_4918_ = l_Lean_Elab_registerDerivingHandler(v___x_4916_, v___x_4917_);
    if crate::leanh::lean_obj_tag(v___x_4918_) == 0 {
        let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4920_: u8 = 0;
        let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_4918_, 1);
        v___x_4919_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_mkHashableInstanceCmds___closed__1;
        v___x_4920_ = 0;
        v___x_4921_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn___closed__25_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_);
        v___x_4922_ = l_Lean_registerTraceClass(v___x_4919_, v___x_4920_, v___x_4921_);
        return v___x_4922_;
    } else {
        return v___x_4918_;
    }
}
pub unsafe fn l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2____boxed(
    mut v_a_4923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4924_ = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_();
    return v_res_4924_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Deriving_Hashable(
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
    res = l___private_Lean_Elab_Deriving_Hashable_0__Lean_Elab_Deriving_Hashable_initFn_00___x40_Lean_Elab_Deriving_Hashable_4079464183____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Deriving_Hashable(
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
pub unsafe fn initialize_Lean_Elab_Deriving_Hashable(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lean_Elab_Deriving_Hashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Deriving_Hashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Deriving_Hashable(builtin);
}

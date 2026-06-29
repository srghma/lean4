// Lean compiler output
// Module: Lean.LibrarySuggestions.SymbolFrequency
// Imports: Lean.Meta.Basic Lean.LibrarySuggestions.Basic
use crate::r#gen::Init::Control::Reader::l_ReaderT_tryFinally___redArg___lam__1;
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_instMonad___redArg, l_instMonadFinallyStateRefT_x27___aux__1___boxed,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_instInhabited;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_firstFrontendMacroScope,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_panic___redArg,
};
use crate::r#gen::Init::System::IO::{
    l_EIO_toBaseIO___boxed, l_instMonadEIO, l_instMonadFinallyEIO___aux__1___boxed,
    l_unsafeBaseIO___redArg,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_CoreM_run_x27___boxed, l_Lean_Core_instMonadCoreM___lam__0___boxed,
    l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl,
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_empty,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_instInhabitedFileMap_default;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_constants, l_Lean_PersistentEnvExtension_getState___redArg,
    l_Lean_registerPersistentEnvExtensionUnsafe___redArg, l_Lean_withoutExporting___redArg,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_toMessageData;
use crate::r#gen::Lean::LibrarySuggestions::Basic::{
    initialize_Lean_LibrarySuggestions_Basic,
    l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit,
    l_Lean_LibrarySuggestions_isDeniedPremise, runtime_initialize_Lean_LibrarySuggestions_Basic,
};
use crate::r#gen::Lean::Message::l_Lean_MessageData_toString;
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l_Lean_Meta_MetaM_run_x27___boxed, l_Lean_Meta_instMonadEnvMetaM,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::OriginalConstKind::l_Lean_wasOriginallyTheorem;
use crate::r#gen::Lean::Util::PtrSet::l_Lean_mkPtrSet___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Balancing::l_Std_DTreeMap_Internal_Impl_balance___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::{
    l_Std_DTreeMap_Internal_Impl_Const_getD___redArg, l_Std_DTreeMap_Internal_Impl_foldl___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_uget_borrowed, lean_mk_array};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set};
static mut l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_LibrarySuggestions_localSymbolFrequencyMap___closed__0_value:
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
    m_fun: l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_LibrarySuggestions_localSymbolFrequencyMap___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LibrarySuggestions_localSymbolFrequencyMap___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_localSymbolFrequencyMapRef: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__6_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_instMonadFinallyEIO___aux__1___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__7_value: crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4) as u16, other: 0, tag: 245 }, m_fun: l_instMonadFinallyStateRefT_x27___aux__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 4, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__8_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_ReaderT_tryFinally___redArg___lam__1 as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__9_value: crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4) as u16, other: 0, tag: 245 }, m_fun: l_instMonadFinallyStateRefT_x27___aux__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 4, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__8_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__10_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_ReaderT_tryFinally___redArg___lam__1 as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0 + 24) as u16, other: 0, tag: 0 }, m_objs: [282574488338432 as *mut crate::leanh::LeanObject,72621647814721793 as *mut crate::leanh::LeanObject,65793 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12: u64 = 0;
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [115, 121, 109, 98, 111, 108, 70, 114, 101, 113, 117, 101, 110, 99, 121, 0]};
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [95, 117, 110, 105, 113, 0]};
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28_value) as *mut crate::leanh::LeanObject,3978731030111751661 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29_value) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__36_value: crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [76, 101, 97, 110, 46, 76, 105, 98, 114, 97, 114, 121, 83, 117, 103, 103, 101, 115, 116, 105, 111, 110, 115, 46, 83, 121, 109, 98, 111, 108, 70, 114, 101, 113, 117, 101, 110, 99, 121, 0]};
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__37_value: crate::leanh::LeanStringObject<83> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 83, m_capacity: 83, m_length: 82, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 76, 105, 98, 114, 97, 114, 121, 83, 117, 103, 103, 101, 115, 116, 105, 111, 110, 115, 46, 83, 121, 109, 98, 111, 108, 70, 114, 101, 113, 117, 101, 110, 99, 121, 46, 48, 46, 76, 101, 97, 110, 46, 69, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 46, 117, 110, 115, 97, 102, 101, 82, 117, 110, 77, 101, 116, 97, 77, 0]};
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__37_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [115, 121, 109, 98, 111, 108, 32, 102, 114, 101, 113, 117, 101, 110, 99, 121, 32, 101, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25_value) as *mut crate::leanh::LeanObject,4785150241512038666 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<8> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*8 + 0) as u16, other: 8, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyMapRef: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instZeroNameMapNat: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__1_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___lam__0(
    mut v_i_x3f_954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_i_x3f_954_) == 0 {
                    v___x_960_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_956_ = v___x_960_;
                    state = 1;
                    continue;
                } else {
                    v_val_961_ = crate::leanh::lean_ctor_get(v_i_x3f_954_, 0);
                    v___y_956_ = v_val_961_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_957_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_958_ = lean_nat_add(v___y_956_, v___x_957_);
                v___x_959_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_959_, 0, v___x_958_);
                return v___x_959_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___lam__0___boxed(
    mut v_i_x3f_962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_963_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___lam__0(v_i_x3f_962_);
    crate::leanh::lean_dec(v_i_x3f_962_);
    return v_res_963_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_964_ = crate::leanh::lean_box(0);
    v___x_965_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___lam__0(v___x_964_);
    return v___x_965_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg(
    mut v_k_966_: *mut crate::leanh::LeanObject,
    mut v_t_967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_975_: u8 = 0;
    let mut v___x_976_: u8 = 0;
    let mut v_impl_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_987_: u8 = 0;
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_967_) == 0 {
                    v_size_968_ = crate::leanh::lean_ctor_get(v_t_967_, 0);
                    v_k_969_ = crate::leanh::lean_ctor_get(v_t_967_, 1);
                    v_v_970_ = crate::leanh::lean_ctor_get(v_t_967_, 2);
                    v_l_971_ = crate::leanh::lean_ctor_get(v_t_967_, 3);
                    v_r_972_ = crate::leanh::lean_ctor_get(v_t_967_, 4);
                    v_isSharedCheck_987_ = (!crate::leanh::lean_is_exclusive(v_t_967_)) as u8;
                    if v_isSharedCheck_987_ == 0 {
                        v___x_974_ = v_t_967_;
                        v_isShared_975_ = v_isSharedCheck_987_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_972_);
                        crate::leanh::lean_inc(v_l_971_);
                        crate::leanh::lean_inc(v_v_970_);
                        crate::leanh::lean_inc(v_k_969_);
                        crate::leanh::lean_inc(v_size_968_);
                        crate::leanh::lean_dec(v_t_967_);
                        v___x_974_ = crate::leanh::lean_box(0);
                        v_isShared_975_ = v_isSharedCheck_987_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_988_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___closed__0_once), _init_l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___closed__0);
                    v_val_989_ = crate::leanh::lean_ctor_get(v___x_988_, 0);
                    v___x_990_ = crate::leanh::lean_unsigned_to_nat(1);
                    crate::leanh::lean_inc(v_val_989_);
                    v___x_991_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_991_, 0, v___x_990_);
                    crate::leanh::lean_ctor_set(v___x_991_, 1, v_k_966_);
                    crate::leanh::lean_ctor_set(v___x_991_, 2, v_val_989_);
                    crate::leanh::lean_ctor_set(v___x_991_, 3, v_t_967_);
                    crate::leanh::lean_ctor_set(v___x_991_, 4, v_t_967_);
                    return v___x_991_;
                }
            }
            1 => {
                v___x_976_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_966_, v_k_969_);
                match v___x_976_ {
                    0 => {
                        crate::leanh::lean_del_object(v___x_974_);
                        crate::leanh::lean_dec(v_size_968_);
                        v_impl_977_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg(v_k_966_, v_l_971_);
                        v___x_978_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                            v_k_969_,
                            v_v_970_,
                            v_impl_977_,
                            v_r_972_,
                        );
                        return v___x_978_;
                    }
                    1 => {
                        crate::leanh::lean_dec(v_k_969_);
                        v___x_979_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_979_, 0, v_v_970_);
                        v___x_980_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___lam__0(v___x_979_);
                        crate::leanh::lean_dec_ref_known(v___x_979_, 1);
                        v_val_981_ = crate::leanh::lean_ctor_get(v___x_980_, 0);
                        crate::leanh::lean_inc(v_val_981_);
                        crate::leanh::lean_dec(v___x_980_);
                        if v_isShared_975_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_974_, 2, v_val_981_);
                            crate::leanh::lean_ctor_set(v___x_974_, 1, v_k_966_);
                            v___x_983_ = v___x_974_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_984_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_984_, 0, v_size_968_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_984_, 1, v_k_966_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_984_, 2, v_val_981_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_984_, 3, v_l_971_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_984_, 4, v_r_972_);
                            v___x_983_ = v_reuseFailAlloc_984_;
                            state = 2;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_del_object(v___x_974_);
                        crate::leanh::lean_dec(v_size_968_);
                        v_impl_985_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg(v_k_966_, v_r_972_);
                        v___x_986_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                            v_k_969_,
                            v_v_970_,
                            v_l_971_,
                            v_impl_985_,
                        );
                        return v___x_986_;
                    }
                }
            }
            2 => {
                return v___x_983_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__0(
    mut v_n_x27_992_: *mut crate::leanh::LeanObject,
    mut v_acc_993_: *mut crate::leanh::LeanObject,
    mut v___y_994_: *mut crate::leanh::LeanObject,
    mut v___y_995_: *mut crate::leanh::LeanObject,
    mut v___y_996_: *mut crate::leanh::LeanObject,
    mut v___y_997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_999_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg(v_n_x27_992_, v_acc_993_);
    v___x_1000_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1000_, 0, v___x_999_);
    return v___x_1000_;
}
pub unsafe fn l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__0___boxed(
    mut v_n_x27_1001_: *mut crate::leanh::LeanObject,
    mut v_acc_1002_: *mut crate::leanh::LeanObject,
    mut v___y_1003_: *mut crate::leanh::LeanObject,
    mut v___y_1004_: *mut crate::leanh::LeanObject,
    mut v___y_1005_: *mut crate::leanh::LeanObject,
    mut v___y_1006_: *mut crate::leanh::LeanObject,
    mut v___y_1007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1008_ = l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__0(
        v_n_x27_1001_,
        v_acc_1002_,
        v___y_1003_,
        v___y_1004_,
        v___y_1005_,
        v___y_1006_,
    );
    crate::leanh::lean_dec(v___y_1006_);
    crate::leanh::lean_dec_ref(v___y_1005_);
    crate::leanh::lean_dec(v___y_1004_);
    crate::leanh::lean_dec_ref(v___y_1003_);
    return v_res_1008_;
}
pub unsafe fn _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1009_ = crate::leanh::lean_unsigned_to_nat(64);
    v___x_1010_ = l_Lean_mkPtrSet___redArg(v___x_1009_);
    return v___x_1010_;
}
pub unsafe fn _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1011_ = crate::leanh::lean_box(0);
    v___x_1012_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1013_ = lean_mk_array(v___x_1012_, v___x_1011_);
    return v___x_1013_;
}
pub unsafe fn _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1014_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__1_once
        ),
        _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__1,
    );
    v___x_1015_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1016_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1016_, 0, v___x_1015_);
    crate::leanh::lean_ctor_set(v___x_1016_, 1, v___x_1014_);
    return v___x_1016_;
}
pub unsafe fn _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1017_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2_once
        ),
        _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2,
    );
    v___x_1018_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__0_once
        ),
        _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__0,
    );
    v___x_1019_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1019_, 0, v___x_1018_);
    crate::leanh::lean_ctor_set(v___x_1019_, 1, v___x_1017_);
    return v___x_1019_;
}
pub unsafe fn l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1(
    mut v___f_1020_: *mut crate::leanh::LeanObject,
    mut v_env_1021_: *mut crate::leanh::LeanObject,
    mut v_acc_1022_: *mut crate::leanh::LeanObject,
    mut v_m_1023_: *mut crate::leanh::LeanObject,
    mut v_ci_1024_: *mut crate::leanh::LeanObject,
    mut v___y_1025_: *mut crate::leanh::LeanObject,
    mut v___y_1026_: *mut crate::leanh::LeanObject,
    mut v___y_1027_: *mut crate::leanh::LeanObject,
    mut v___y_1028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1031_: u8 = 0;
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1038_: u8 = 0;
    let mut v_fst_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1043_: u8 = 0;
    let mut v_a_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1047_: u8 = 0;
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1051_: u8 = 0;
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: u8 = 0;
    let mut v___x_1054_: u8 = 0;
    let mut v___x_1055_: u8 = 0;
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1053_ = 0;
                crate::leanh::lean_inc(v_m_1023_);
                crate::leanh::lean_inc_ref(v_env_1021_);
                v___x_1054_ =
                    l_Lean_LibrarySuggestions_isDeniedPremise(v_env_1021_, v_m_1023_, v___x_1053_);
                if v___x_1054_ == 0 {
                    v___x_1055_ = l_Lean_wasOriginallyTheorem(v_env_1021_, v_m_1023_);
                    if v___x_1055_ == 0 {
                        crate::leanh::lean_dec_ref(v___f_1020_);
                        v___x_1056_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1056_, 0, v_acc_1022_);
                        return v___x_1056_;
                    } else {
                        v___y_1031_ = v___x_1054_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_m_1023_);
                    crate::leanh::lean_dec_ref(v_env_1021_);
                    v___y_1031_ = v___x_1054_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1031_ == 0 {
                    v___x_1032_ = l_Lean_ConstantInfo_type(v_ci_1024_);
                    v___x_1033_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__3), core::ptr::addr_of_mut!(l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__3_once), _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__3);
                    v___x_1034_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit(crate::leanh::lean_box(0), v___f_1020_, v___x_1032_, v_acc_1022_, v___x_1033_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
                    if crate::leanh::lean_obj_tag(v___x_1034_) == 0 {
                        v_a_1035_ = crate::leanh::lean_ctor_get(v___x_1034_, 0);
                        v_isSharedCheck_1043_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1034_)) as u8;
                        if v_isSharedCheck_1043_ == 0 {
                            v___x_1037_ = v___x_1034_;
                            v_isShared_1038_ = v_isSharedCheck_1043_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1035_);
                            crate::leanh::lean_dec(v___x_1034_);
                            v___x_1037_ = crate::leanh::lean_box(0);
                            v_isShared_1038_ = v_isSharedCheck_1043_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1044_ = crate::leanh::lean_ctor_get(v___x_1034_, 0);
                        v_isSharedCheck_1051_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1034_)) as u8;
                        if v_isSharedCheck_1051_ == 0 {
                            v___x_1046_ = v___x_1034_;
                            v_isShared_1047_ = v_isSharedCheck_1051_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1044_);
                            crate::leanh::lean_dec(v___x_1034_);
                            v___x_1046_ = crate::leanh::lean_box(0);
                            v_isShared_1047_ = v_isSharedCheck_1051_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_1020_);
                    v___x_1052_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1052_, 0, v_acc_1022_);
                    return v___x_1052_;
                }
            }
            2 => {
                v_fst_1039_ = crate::leanh::lean_ctor_get(v_a_1035_, 0);
                crate::leanh::lean_inc(v_fst_1039_);
                crate::leanh::lean_dec(v_a_1035_);
                if v_isShared_1038_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1037_, 0, v_fst_1039_);
                    v___x_1041_ = v___x_1037_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1042_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_fst_1039_);
                    v___x_1041_ = v_reuseFailAlloc_1042_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1041_;
            }
            4 => {
                if v_isShared_1047_ == 0 {
                    v___x_1049_ = v___x_1046_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1050_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
                    v___x_1049_ = v_reuseFailAlloc_1050_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1049_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___boxed(
    mut v___f_1057_: *mut crate::leanh::LeanObject,
    mut v_env_1058_: *mut crate::leanh::LeanObject,
    mut v_acc_1059_: *mut crate::leanh::LeanObject,
    mut v_m_1060_: *mut crate::leanh::LeanObject,
    mut v_ci_1061_: *mut crate::leanh::LeanObject,
    mut v___y_1062_: *mut crate::leanh::LeanObject,
    mut v___y_1063_: *mut crate::leanh::LeanObject,
    mut v___y_1064_: *mut crate::leanh::LeanObject,
    mut v___y_1065_: *mut crate::leanh::LeanObject,
    mut v___y_1066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1067_ = l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1(
        v___f_1057_,
        v_env_1058_,
        v_acc_1059_,
        v_m_1060_,
        v_ci_1061_,
        v___y_1062_,
        v___y_1063_,
        v___y_1064_,
        v___y_1065_,
    );
    crate::leanh::lean_dec(v___y_1065_);
    crate::leanh::lean_dec_ref(v___y_1064_);
    crate::leanh::lean_dec(v___y_1063_);
    crate::leanh::lean_dec_ref(v___y_1062_);
    crate::leanh::lean_dec_ref(v_ci_1061_);
    return v_res_1067_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___redArg(
    mut v_f_1068_: *mut crate::leanh::LeanObject,
    mut v_keys_1069_: *mut crate::leanh::LeanObject,
    mut v_vals_1070_: *mut crate::leanh::LeanObject,
    mut v_i_1071_: *mut crate::leanh::LeanObject,
    mut v_acc_1072_: *mut crate::leanh::LeanObject,
    mut v___y_1073_: *mut crate::leanh::LeanObject,
    mut v___y_1074_: *mut crate::leanh::LeanObject,
    mut v___y_1075_: *mut crate::leanh::LeanObject,
    mut v___y_1076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: u8 = 0;
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1078_ = lean_array_get_size(v_keys_1069_);
                v___x_1079_ = lean_nat_dec_lt(v_i_1071_, v___x_1078_);
                if v___x_1079_ == 0 {
                    crate::leanh::lean_dec(v_i_1071_);
                    crate::leanh::lean_dec_ref(v_f_1068_);
                    v___x_1080_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1080_, 0, v_acc_1072_);
                    return v___x_1080_;
                } else {
                    v_k_1081_ = lean_array_fget_borrowed(v_keys_1069_, v_i_1071_);
                    v_v_1082_ = lean_array_fget_borrowed(v_vals_1070_, v_i_1071_);
                    crate::leanh::lean_inc_ref(v_f_1068_);
                    crate::leanh::lean_inc(v___y_1076_);
                    crate::leanh::lean_inc_ref(v___y_1075_);
                    crate::leanh::lean_inc(v___y_1074_);
                    crate::leanh::lean_inc_ref(v___y_1073_);
                    crate::leanh::lean_inc(v_v_1082_);
                    crate::leanh::lean_inc(v_k_1081_);
                    v___x_1083_ = crate::leanh::lean_apply_8(
                        v_f_1068_,
                        v_acc_1072_,
                        v_k_1081_,
                        v_v_1082_,
                        v___y_1073_,
                        v___y_1074_,
                        v___y_1075_,
                        v___y_1076_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_1083_) == 0 {
                        v_a_1084_ = crate::leanh::lean_ctor_get(v___x_1083_, 0);
                        crate::leanh::lean_inc(v_a_1084_);
                        crate::leanh::lean_dec_ref_known(v___x_1083_, 1);
                        v___x_1085_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1086_ = lean_nat_add(v_i_1071_, v___x_1085_);
                        crate::leanh::lean_dec(v_i_1071_);
                        v_i_1071_ = v___x_1086_;
                        v_acc_1072_ = v_a_1084_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_1071_);
                        crate::leanh::lean_dec_ref(v_f_1068_);
                        return v___x_1083_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_f_1088_: *mut crate::leanh::LeanObject,
    mut v_keys_1089_: *mut crate::leanh::LeanObject,
    mut v_vals_1090_: *mut crate::leanh::LeanObject,
    mut v_i_1091_: *mut crate::leanh::LeanObject,
    mut v_acc_1092_: *mut crate::leanh::LeanObject,
    mut v___y_1093_: *mut crate::leanh::LeanObject,
    mut v___y_1094_: *mut crate::leanh::LeanObject,
    mut v___y_1095_: *mut crate::leanh::LeanObject,
    mut v___y_1096_: *mut crate::leanh::LeanObject,
    mut v___y_1097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1098_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___redArg(v_f_1088_, v_keys_1089_, v_vals_1090_, v_i_1091_, v_acc_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
    crate::leanh::lean_dec(v___y_1096_);
    crate::leanh::lean_dec_ref(v___y_1095_);
    crate::leanh::lean_dec(v___y_1094_);
    crate::leanh::lean_dec_ref(v___y_1093_);
    crate::leanh::lean_dec_ref(v_vals_1090_);
    crate::leanh::lean_dec_ref(v_keys_1089_);
    return v_res_1098_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(
    mut v_f_1099_: *mut crate::leanh::LeanObject,
    mut v_x_1100_: *mut crate::leanh::LeanObject,
    mut v_x_1101_: *mut crate::leanh::LeanObject,
    mut v___y_1102_: *mut crate::leanh::LeanObject,
    mut v___y_1103_: *mut crate::leanh::LeanObject,
    mut v___y_1104_: *mut crate::leanh::LeanObject,
    mut v___y_1105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1110_: u8 = 0;
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: u8 = 0;
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: u8 = 0;
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: usize = 0;
    let mut v___x_1122_: usize = 0;
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: usize = 0;
    let mut v___x_1125_: usize = 0;
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1127_: u8 = 0;
    let mut v_ks_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1100_) == 0 {
                    v_es_1107_ = crate::leanh::lean_ctor_get(v_x_1100_, 0);
                    v_isSharedCheck_1127_ = (!crate::leanh::lean_is_exclusive(v_x_1100_)) as u8;
                    if v_isSharedCheck_1127_ == 0 {
                        v___x_1109_ = v_x_1100_;
                        v_isShared_1110_ = v_isSharedCheck_1127_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_es_1107_);
                        crate::leanh::lean_dec(v_x_1100_);
                        v___x_1109_ = crate::leanh::lean_box(0);
                        v_isShared_1110_ = v_isSharedCheck_1127_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_1128_ = crate::leanh::lean_ctor_get(v_x_1100_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1128_);
                    v_vs_1129_ = crate::leanh::lean_ctor_get(v_x_1100_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1129_);
                    crate::leanh::lean_dec_ref_known(v_x_1100_, 2);
                    v___x_1130_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1131_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___redArg(v_f_1099_, v_ks_1128_, v_vs_1129_, v___x_1130_, v_x_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
                    crate::leanh::lean_dec_ref(v_vs_1129_);
                    crate::leanh::lean_dec_ref(v_ks_1128_);
                    return v___x_1131_;
                }
            }
            1 => {
                v___x_1111_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1112_ = lean_array_get_size(v_es_1107_);
                v___x_1113_ = lean_nat_dec_lt(v___x_1111_, v___x_1112_);
                if v___x_1113_ == 0 {
                    crate::leanh::lean_dec_ref(v_es_1107_);
                    crate::leanh::lean_dec_ref(v_f_1099_);
                    if v_isShared_1110_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1109_, 0, v_x_1101_);
                        v___x_1115_ = v___x_1109_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1116_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_x_1101_);
                        v___x_1115_ = v_reuseFailAlloc_1116_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1117_ = lean_nat_dec_le(v___x_1112_, v___x_1112_);
                    if v___x_1117_ == 0 {
                        if v___x_1113_ == 0 {
                            crate::leanh::lean_dec_ref(v_es_1107_);
                            crate::leanh::lean_dec_ref(v_f_1099_);
                            if v_isShared_1110_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1109_, 0, v_x_1101_);
                                v___x_1119_ = v___x_1109_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1120_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_x_1101_);
                                v___x_1119_ = v_reuseFailAlloc_1120_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1109_);
                            v___x_1121_ = 0usize;
                            v___x_1122_ = lean_usize_of_nat(v___x_1112_);
                            v___x_1123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(v_f_1099_, v_es_1107_, v___x_1121_, v___x_1122_, v_x_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
                            crate::leanh::lean_dec_ref(v_es_1107_);
                            return v___x_1123_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1109_);
                        v___x_1124_ = 0usize;
                        v___x_1125_ = lean_usize_of_nat(v___x_1112_);
                        v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(v_f_1099_, v_es_1107_, v___x_1124_, v___x_1125_, v_x_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
                        crate::leanh::lean_dec_ref(v_es_1107_);
                        return v___x_1126_;
                    }
                }
            }
            2 => {
                return v___x_1115_;
            }
            3 => {
                return v___x_1119_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(
    mut v_f_1132_: *mut crate::leanh::LeanObject,
    mut v_as_1133_: *mut crate::leanh::LeanObject,
    mut v_i_1134_: usize,
    mut v_stop_1135_: usize,
    mut v_b_1136_: *mut crate::leanh::LeanObject,
    mut v___y_1137_: *mut crate::leanh::LeanObject,
    mut v___y_1138_: *mut crate::leanh::LeanObject,
    mut v___y_1139_: *mut crate::leanh::LeanObject,
    mut v___y_1140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: usize = 0;
    let mut v___x_1145_: usize = 0;
    let mut v___y_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: u8 = 0;
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1150_ = lean_usize_dec_eq(v_i_1134_, v_stop_1135_);
                if v___x_1150_ == 0 {
                    v___x_1151_ = lean_array_uget_borrowed(v_as_1133_, v_i_1134_);
                    match crate::leanh::lean_obj_tag(v___x_1151_) {
                        0 => {
                            v_key_1152_ = crate::leanh::lean_ctor_get(v___x_1151_, 0);
                            v_val_1153_ = crate::leanh::lean_ctor_get(v___x_1151_, 1);
                            crate::leanh::lean_inc_ref(v_f_1132_);
                            crate::leanh::lean_inc(v___y_1140_);
                            crate::leanh::lean_inc_ref(v___y_1139_);
                            crate::leanh::lean_inc(v___y_1138_);
                            crate::leanh::lean_inc_ref(v___y_1137_);
                            crate::leanh::lean_inc(v_val_1153_);
                            crate::leanh::lean_inc(v_key_1152_);
                            v___x_1154_ = crate::leanh::lean_apply_8(
                                v_f_1132_,
                                v_b_1136_,
                                v_key_1152_,
                                v_val_1153_,
                                v___y_1137_,
                                v___y_1138_,
                                v___y_1139_,
                                v___y_1140_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_1148_ = v___x_1154_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_1155_ = crate::leanh::lean_ctor_get(v___x_1151_, 0);
                            crate::leanh::lean_inc(v_node_1155_);
                            crate::leanh::lean_inc_ref(v_f_1132_);
                            v___x_1156_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_1132_, v_node_1155_, v_b_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
                            v___y_1148_ = v___x_1156_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_a_1143_ = v_b_1136_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_1132_);
                    v___x_1157_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1157_, 0, v_b_1136_);
                    return v___x_1157_;
                }
            }
            1 => {
                v___x_1144_ = 1usize;
                v___x_1145_ = lean_usize_add(v_i_1134_, v___x_1144_);
                v_i_1134_ = v___x_1145_;
                v_b_1136_ = v_a_1143_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_1148_) == 0 {
                    v_a_1149_ = crate::leanh::lean_ctor_get(v___y_1148_, 0);
                    crate::leanh::lean_inc(v_a_1149_);
                    crate::leanh::lean_dec_ref_known(v___y_1148_, 1);
                    v_a_1143_ = v_a_1149_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_f_1132_);
                    return v___y_1148_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_f_1158_: *mut crate::leanh::LeanObject,
    mut v_as_1159_: *mut crate::leanh::LeanObject,
    mut v_i_1160_: *mut crate::leanh::LeanObject,
    mut v_stop_1161_: *mut crate::leanh::LeanObject,
    mut v_b_1162_: *mut crate::leanh::LeanObject,
    mut v___y_1163_: *mut crate::leanh::LeanObject,
    mut v___y_1164_: *mut crate::leanh::LeanObject,
    mut v___y_1165_: *mut crate::leanh::LeanObject,
    mut v___y_1166_: *mut crate::leanh::LeanObject,
    mut v___y_1167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1168_: usize = 0;
    let mut v_stop_boxed_1169_: usize = 0;
    let mut v_res_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1168_ = crate::leanh::lean_unbox_usize(v_i_1160_);
    crate::leanh::lean_dec(v_i_1160_);
    v_stop_boxed_1169_ = crate::leanh::lean_unbox_usize(v_stop_1161_);
    crate::leanh::lean_dec(v_stop_1161_);
    v_res_1170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(v_f_1158_, v_as_1159_, v_i_boxed_1168_, v_stop_boxed_1169_, v_b_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
    crate::leanh::lean_dec(v___y_1166_);
    crate::leanh::lean_dec_ref(v___y_1165_);
    crate::leanh::lean_dec(v___y_1164_);
    crate::leanh::lean_dec_ref(v___y_1163_);
    crate::leanh::lean_dec_ref(v_as_1159_);
    return v_res_1170_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg___boxed(
    mut v_f_1171_: *mut crate::leanh::LeanObject,
    mut v_x_1172_: *mut crate::leanh::LeanObject,
    mut v_x_1173_: *mut crate::leanh::LeanObject,
    mut v___y_1174_: *mut crate::leanh::LeanObject,
    mut v___y_1175_: *mut crate::leanh::LeanObject,
    mut v___y_1176_: *mut crate::leanh::LeanObject,
    mut v___y_1177_: *mut crate::leanh::LeanObject,
    mut v___y_1178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1179_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_1171_, v_x_1172_, v_x_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
    crate::leanh::lean_dec(v___y_1177_);
    crate::leanh::lean_dec_ref(v___y_1176_);
    crate::leanh::lean_dec(v___y_1175_);
    crate::leanh::lean_dec_ref(v___y_1174_);
    return v_res_1179_;
}
pub unsafe fn l_Lean_LibrarySuggestions_localSymbolFrequencyMap(
    mut v_a_1181_: *mut crate::leanh::LeanObject,
    mut v_a_1182_: *mut crate::leanh::LeanObject,
    mut v_a_1183_: *mut crate::leanh::LeanObject,
    mut v_a_1184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1186_ = lean_st_ref_get(v_a_1184_);
    v_env_1187_ = crate::leanh::lean_ctor_get(v___x_1186_, 0);
    crate::leanh::lean_inc_ref_n(v_env_1187_, 2);
    crate::leanh::lean_dec(v___x_1186_);
    v___x_1188_ = l_Lean_Environment_constants(v_env_1187_);
    v_map_u2082_1189_ = crate::leanh::lean_ctor_get(v___x_1188_, 1);
    crate::leanh::lean_inc_ref(v_map_u2082_1189_);
    crate::leanh::lean_dec_ref(v___x_1188_);
    v___f_1190_ = l_Lean_LibrarySuggestions_localSymbolFrequencyMap___closed__0;
    v___f_1191_ = crate::leanh::lean_alloc_closure(
        l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___boxed
            as *mut core::ffi::c_void,
        10,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1191_, 0, v___f_1190_);
    crate::leanh::lean_closure_set(v___f_1191_, 1, v_env_1187_);
    v___x_1192_ = crate::leanh::lean_box(1);
    v___x_1193_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v___f_1191_, v_map_u2082_1189_, v___x_1192_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
    return v___x_1193_;
}
pub unsafe fn l_Lean_LibrarySuggestions_localSymbolFrequencyMap___boxed(
    mut v_a_1194_: *mut crate::leanh::LeanObject,
    mut v_a_1195_: *mut crate::leanh::LeanObject,
    mut v_a_1196_: *mut crate::leanh::LeanObject,
    mut v_a_1197_: *mut crate::leanh::LeanObject,
    mut v_a_1198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1199_ = l_Lean_LibrarySuggestions_localSymbolFrequencyMap(
        v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_,
    );
    crate::leanh::lean_dec(v_a_1197_);
    crate::leanh::lean_dec_ref(v_a_1196_);
    crate::leanh::lean_dec(v_a_1195_);
    crate::leanh::lean_dec_ref(v_a_1194_);
    return v_res_1199_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0(
    mut v_k_1200_: *mut crate::leanh::LeanObject,
    mut v_t_1201_: *mut crate::leanh::LeanObject,
    mut v_hl_1202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1203_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg(v_k_1200_, v_t_1201_);
    return v___x_1203_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1___redArg(
    mut v_map_1204_: *mut crate::leanh::LeanObject,
    mut v_f_1205_: *mut crate::leanh::LeanObject,
    mut v_init_1206_: *mut crate::leanh::LeanObject,
    mut v___y_1207_: *mut crate::leanh::LeanObject,
    mut v___y_1208_: *mut crate::leanh::LeanObject,
    mut v___y_1209_: *mut crate::leanh::LeanObject,
    mut v___y_1210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1212_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_1205_, v_map_1204_, v_init_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
    return v___x_1212_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1___redArg___boxed(
    mut v_map_1213_: *mut crate::leanh::LeanObject,
    mut v_f_1214_: *mut crate::leanh::LeanObject,
    mut v_init_1215_: *mut crate::leanh::LeanObject,
    mut v___y_1216_: *mut crate::leanh::LeanObject,
    mut v___y_1217_: *mut crate::leanh::LeanObject,
    mut v___y_1218_: *mut crate::leanh::LeanObject,
    mut v___y_1219_: *mut crate::leanh::LeanObject,
    mut v___y_1220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1221_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1___redArg(v_map_1213_, v_f_1214_, v_init_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
    crate::leanh::lean_dec(v___y_1219_);
    crate::leanh::lean_dec_ref(v___y_1218_);
    crate::leanh::lean_dec(v___y_1217_);
    crate::leanh::lean_dec_ref(v___y_1216_);
    return v_res_1221_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1(
    mut v_00_u03c3_1222_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1223_: *mut crate::leanh::LeanObject,
    mut v_map_1224_: *mut crate::leanh::LeanObject,
    mut v_f_1225_: *mut crate::leanh::LeanObject,
    mut v_init_1226_: *mut crate::leanh::LeanObject,
    mut v___y_1227_: *mut crate::leanh::LeanObject,
    mut v___y_1228_: *mut crate::leanh::LeanObject,
    mut v___y_1229_: *mut crate::leanh::LeanObject,
    mut v___y_1230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1232_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_1225_, v_map_1224_, v_init_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
    return v___x_1232_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1___boxed(
    mut v_00_u03c3_1233_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1234_: *mut crate::leanh::LeanObject,
    mut v_map_1235_: *mut crate::leanh::LeanObject,
    mut v_f_1236_: *mut crate::leanh::LeanObject,
    mut v_init_1237_: *mut crate::leanh::LeanObject,
    mut v___y_1238_: *mut crate::leanh::LeanObject,
    mut v___y_1239_: *mut crate::leanh::LeanObject,
    mut v___y_1240_: *mut crate::leanh::LeanObject,
    mut v___y_1241_: *mut crate::leanh::LeanObject,
    mut v___y_1242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1243_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1(v_00_u03c3_1233_, v_00_u03b2_1234_, v_map_1235_, v_f_1236_, v_init_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
    crate::leanh::lean_dec(v___y_1241_);
    crate::leanh::lean_dec_ref(v___y_1240_);
    crate::leanh::lean_dec(v___y_1239_);
    crate::leanh::lean_dec_ref(v___y_1238_);
    return v_res_1243_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1(
    mut v_00_u03c3_1244_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1245_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1246_: *mut crate::leanh::LeanObject,
    mut v_f_1247_: *mut crate::leanh::LeanObject,
    mut v_x_1248_: *mut crate::leanh::LeanObject,
    mut v_x_1249_: *mut crate::leanh::LeanObject,
    mut v___y_1250_: *mut crate::leanh::LeanObject,
    mut v___y_1251_: *mut crate::leanh::LeanObject,
    mut v___y_1252_: *mut crate::leanh::LeanObject,
    mut v___y_1253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1255_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_1247_, v_x_1248_, v_x_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
    return v___x_1255_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___boxed(
    mut v_00_u03c3_1256_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1257_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1258_: *mut crate::leanh::LeanObject,
    mut v_f_1259_: *mut crate::leanh::LeanObject,
    mut v_x_1260_: *mut crate::leanh::LeanObject,
    mut v_x_1261_: *mut crate::leanh::LeanObject,
    mut v___y_1262_: *mut crate::leanh::LeanObject,
    mut v___y_1263_: *mut crate::leanh::LeanObject,
    mut v___y_1264_: *mut crate::leanh::LeanObject,
    mut v___y_1265_: *mut crate::leanh::LeanObject,
    mut v___y_1266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1267_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1(v_00_u03c3_1256_, v_00_u03b1_1257_, v_00_u03b2_1258_, v_f_1259_, v_x_1260_, v_x_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
    crate::leanh::lean_dec(v___y_1265_);
    crate::leanh::lean_dec_ref(v___y_1264_);
    crate::leanh::lean_dec(v___y_1263_);
    crate::leanh::lean_dec_ref(v___y_1262_);
    return v_res_1267_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2(
    mut v_00_u03b1_1268_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1269_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1270_: *mut crate::leanh::LeanObject,
    mut v_f_1271_: *mut crate::leanh::LeanObject,
    mut v_as_1272_: *mut crate::leanh::LeanObject,
    mut v_i_1273_: usize,
    mut v_stop_1274_: usize,
    mut v_b_1275_: *mut crate::leanh::LeanObject,
    mut v___y_1276_: *mut crate::leanh::LeanObject,
    mut v___y_1277_: *mut crate::leanh::LeanObject,
    mut v___y_1278_: *mut crate::leanh::LeanObject,
    mut v___y_1279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(v_f_1271_, v_as_1272_, v_i_1273_, v_stop_1274_, v_b_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
    return v___x_1281_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b1_1282_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1283_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1284_: *mut crate::leanh::LeanObject,
    mut v_f_1285_: *mut crate::leanh::LeanObject,
    mut v_as_1286_: *mut crate::leanh::LeanObject,
    mut v_i_1287_: *mut crate::leanh::LeanObject,
    mut v_stop_1288_: *mut crate::leanh::LeanObject,
    mut v_b_1289_: *mut crate::leanh::LeanObject,
    mut v___y_1290_: *mut crate::leanh::LeanObject,
    mut v___y_1291_: *mut crate::leanh::LeanObject,
    mut v___y_1292_: *mut crate::leanh::LeanObject,
    mut v___y_1293_: *mut crate::leanh::LeanObject,
    mut v___y_1294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1295_: usize = 0;
    let mut v_stop_boxed_1296_: usize = 0;
    let mut v_res_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1295_ = crate::leanh::lean_unbox_usize(v_i_1287_);
    crate::leanh::lean_dec(v_i_1287_);
    v_stop_boxed_1296_ = crate::leanh::lean_unbox_usize(v_stop_1288_);
    crate::leanh::lean_dec(v_stop_1288_);
    v_res_1297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2(v_00_u03b1_1282_, v_00_u03b2_1283_, v_00_u03c3_1284_, v_f_1285_, v_as_1286_, v_i_boxed_1295_, v_stop_boxed_1296_, v_b_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
    crate::leanh::lean_dec(v___y_1293_);
    crate::leanh::lean_dec_ref(v___y_1292_);
    crate::leanh::lean_dec(v___y_1291_);
    crate::leanh::lean_dec_ref(v___y_1290_);
    crate::leanh::lean_dec_ref(v_as_1286_);
    return v_res_1297_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3(
    mut v_00_u03c3_1298_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1299_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1300_: *mut crate::leanh::LeanObject,
    mut v_f_1301_: *mut crate::leanh::LeanObject,
    mut v_keys_1302_: *mut crate::leanh::LeanObject,
    mut v_vals_1303_: *mut crate::leanh::LeanObject,
    mut v_heq_1304_: *mut crate::leanh::LeanObject,
    mut v_i_1305_: *mut crate::leanh::LeanObject,
    mut v_acc_1306_: *mut crate::leanh::LeanObject,
    mut v___y_1307_: *mut crate::leanh::LeanObject,
    mut v___y_1308_: *mut crate::leanh::LeanObject,
    mut v___y_1309_: *mut crate::leanh::LeanObject,
    mut v___y_1310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1312_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___redArg(v_f_1301_, v_keys_1302_, v_vals_1303_, v_i_1305_, v_acc_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
    return v___x_1312_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___boxed(
    mut v_00_u03c3_1313_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1314_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1315_: *mut crate::leanh::LeanObject,
    mut v_f_1316_: *mut crate::leanh::LeanObject,
    mut v_keys_1317_: *mut crate::leanh::LeanObject,
    mut v_vals_1318_: *mut crate::leanh::LeanObject,
    mut v_heq_1319_: *mut crate::leanh::LeanObject,
    mut v_i_1320_: *mut crate::leanh::LeanObject,
    mut v_acc_1321_: *mut crate::leanh::LeanObject,
    mut v___y_1322_: *mut crate::leanh::LeanObject,
    mut v___y_1323_: *mut crate::leanh::LeanObject,
    mut v___y_1324_: *mut crate::leanh::LeanObject,
    mut v___y_1325_: *mut crate::leanh::LeanObject,
    mut v___y_1326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1327_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3(v_00_u03c3_1313_, v_00_u03b1_1314_, v_00_u03b2_1315_, v_f_1316_, v_keys_1317_, v_vals_1318_, v_heq_1319_, v_i_1320_, v_acc_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
    crate::leanh::lean_dec(v___y_1325_);
    crate::leanh::lean_dec_ref(v___y_1324_);
    crate::leanh::lean_dec(v___y_1323_);
    crate::leanh::lean_dec_ref(v___y_1322_);
    crate::leanh::lean_dec_ref(v_vals_1318_);
    crate::leanh::lean_dec_ref(v_keys_1317_);
    return v_res_1327_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1329_ = crate::leanh::lean_box(0);
    v___x_1330_ = lean_st_mk_ref(v___x_1329_);
    v___x_1331_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1331_, 0, v___x_1330_);
    return v___x_1331_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2____boxed(
    mut v_a_1332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1333_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2_();
    return v_res_1333_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap(
    mut v_a_1334_: *mut crate::leanh::LeanObject,
    mut v_a_1335_: *mut crate::leanh::LeanObject,
    mut v_a_1336_: *mut crate::leanh::LeanObject,
    mut v_a_1337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1345_: u8 = 0;
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1351_: u8 = 0;
    let mut v_val_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1355_: u8 = 0;
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1359_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1339_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_localSymbolFrequencyMapRef;
                v___x_1340_ = lean_st_ref_get(v___x_1339_);
                if crate::leanh::lean_obj_tag(v___x_1340_) == 0 {
                    v___x_1341_ = l_Lean_LibrarySuggestions_localSymbolFrequencyMap(
                        v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1341_) == 0 {
                        v_a_1342_ = crate::leanh::lean_ctor_get(v___x_1341_, 0);
                        v_isSharedCheck_1351_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1341_)) as u8;
                        if v_isSharedCheck_1351_ == 0 {
                            v___x_1344_ = v___x_1341_;
                            v_isShared_1345_ = v_isSharedCheck_1351_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1342_);
                            crate::leanh::lean_dec(v___x_1341_);
                            v___x_1344_ = crate::leanh::lean_box(0);
                            v_isShared_1345_ = v_isSharedCheck_1351_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_1341_;
                    }
                } else {
                    v_val_1352_ = crate::leanh::lean_ctor_get(v___x_1340_, 0);
                    v_isSharedCheck_1359_ = (!crate::leanh::lean_is_exclusive(v___x_1340_)) as u8;
                    if v_isSharedCheck_1359_ == 0 {
                        v___x_1354_ = v___x_1340_;
                        v_isShared_1355_ = v_isSharedCheck_1359_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1352_);
                        crate::leanh::lean_dec(v___x_1340_);
                        v___x_1354_ = crate::leanh::lean_box(0);
                        v_isShared_1355_ = v_isSharedCheck_1359_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_1342_);
                v___x_1346_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1346_, 0, v_a_1342_);
                v___x_1347_ = lean_st_ref_set(v___x_1339_, v___x_1346_);
                if v_isShared_1345_ == 0 {
                    v___x_1349_ = v___x_1344_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1350_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1342_);
                    v___x_1349_ = v_reuseFailAlloc_1350_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1349_;
            }
            3 => {
                if v_isShared_1355_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1354_, 0);
                    v___x_1357_ = v___x_1354_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1358_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_val_1352_);
                    v___x_1357_ = v_reuseFailAlloc_1358_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1357_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap___boxed(
    mut v_a_1360_: *mut crate::leanh::LeanObject,
    mut v_a_1361_: *mut crate::leanh::LeanObject,
    mut v_a_1362_: *mut crate::leanh::LeanObject,
    mut v_a_1363_: *mut crate::leanh::LeanObject,
    mut v_a_1364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1365_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap(v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
    crate::leanh::lean_dec(v_a_1363_);
    crate::leanh::lean_dec_ref(v_a_1362_);
    crate::leanh::lean_dec(v_a_1361_);
    crate::leanh::lean_dec_ref(v_a_1360_);
    return v_res_1365_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(
    mut v_t_1366_: *mut crate::leanh::LeanObject,
    mut v_k_1367_: *mut crate::leanh::LeanObject,
    mut v_fallback_1368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1366_) == 0 {
                    v_k_1369_ = crate::leanh::lean_ctor_get(v_t_1366_, 1);
                    v_v_1370_ = crate::leanh::lean_ctor_get(v_t_1366_, 2);
                    v_l_1371_ = crate::leanh::lean_ctor_get(v_t_1366_, 3);
                    v_r_1372_ = crate::leanh::lean_ctor_get(v_t_1366_, 4);
                    v___x_1373_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1367_, v_k_1369_);
                    match v___x_1373_ {
                        0 => {
                            v_t_1366_ = v_l_1371_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_1370_);
                            return v_v_1370_;
                        }
                        _ => {
                            v_t_1366_ = v_r_1372_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_fallback_1368_);
                    return v_fallback_1368_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg___boxed(
    mut v_t_1376_: *mut crate::leanh::LeanObject,
    mut v_k_1377_: *mut crate::leanh::LeanObject,
    mut v_fallback_1378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1379_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_t_1376_, v_k_1377_, v_fallback_1378_);
    crate::leanh::lean_dec(v_fallback_1378_);
    crate::leanh::lean_dec(v_k_1377_);
    crate::leanh::lean_dec(v_t_1376_);
    return v_res_1379_;
}
pub unsafe fn l_Lean_LibrarySuggestions_localSymbolFrequency(
    mut v_n_1380_: *mut crate::leanh::LeanObject,
    mut v_a_1381_: *mut crate::leanh::LeanObject,
    mut v_a_1382_: *mut crate::leanh::LeanObject,
    mut v_a_1383_: *mut crate::leanh::LeanObject,
    mut v_a_1384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1390_: u8 = 0;
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1396_: u8 = 0;
    let mut v_a_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1400_: u8 = 0;
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1404_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1386_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap(v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
                if crate::leanh::lean_obj_tag(v___x_1386_) == 0 {
                    v_a_1387_ = crate::leanh::lean_ctor_get(v___x_1386_, 0);
                    v_isSharedCheck_1396_ = (!crate::leanh::lean_is_exclusive(v___x_1386_)) as u8;
                    if v_isSharedCheck_1396_ == 0 {
                        v___x_1389_ = v___x_1386_;
                        v_isShared_1390_ = v_isSharedCheck_1396_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1387_);
                        crate::leanh::lean_dec(v___x_1386_);
                        v___x_1389_ = crate::leanh::lean_box(0);
                        v_isShared_1390_ = v_isSharedCheck_1396_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1397_ = crate::leanh::lean_ctor_get(v___x_1386_, 0);
                    v_isSharedCheck_1404_ = (!crate::leanh::lean_is_exclusive(v___x_1386_)) as u8;
                    if v_isSharedCheck_1404_ == 0 {
                        v___x_1399_ = v___x_1386_;
                        v_isShared_1400_ = v_isSharedCheck_1404_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1397_);
                        crate::leanh::lean_dec(v___x_1386_);
                        v___x_1399_ = crate::leanh::lean_box(0);
                        v_isShared_1400_ = v_isSharedCheck_1404_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1391_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1392_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_a_1387_, v_n_1380_, v___x_1391_);
                crate::leanh::lean_dec(v_a_1387_);
                if v_isShared_1390_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1389_, 0, v___x_1392_);
                    v___x_1394_ = v___x_1389_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1395_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
                    v___x_1394_ = v_reuseFailAlloc_1395_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1394_;
            }
            3 => {
                if v_isShared_1400_ == 0 {
                    v___x_1402_ = v___x_1399_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1403_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
                    v___x_1402_ = v_reuseFailAlloc_1403_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1402_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_LibrarySuggestions_localSymbolFrequency___boxed(
    mut v_n_1405_: *mut crate::leanh::LeanObject,
    mut v_a_1406_: *mut crate::leanh::LeanObject,
    mut v_a_1407_: *mut crate::leanh::LeanObject,
    mut v_a_1408_: *mut crate::leanh::LeanObject,
    mut v_a_1409_: *mut crate::leanh::LeanObject,
    mut v_a_1410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1411_ = l_Lean_LibrarySuggestions_localSymbolFrequency(
        v_n_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_,
    );
    crate::leanh::lean_dec(v_a_1409_);
    crate::leanh::lean_dec_ref(v_a_1408_);
    crate::leanh::lean_dec(v_a_1407_);
    crate::leanh::lean_dec_ref(v_a_1406_);
    crate::leanh::lean_dec(v_n_1405_);
    return v_res_1411_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0(
    mut v_00_u03b4_1412_: *mut crate::leanh::LeanObject,
    mut v_t_1413_: *mut crate::leanh::LeanObject,
    mut v_k_1414_: *mut crate::leanh::LeanObject,
    mut v_fallback_1415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1416_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_t_1413_, v_k_1414_, v_fallback_1415_);
    return v___x_1416_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___boxed(
    mut v_00_u03b4_1417_: *mut crate::leanh::LeanObject,
    mut v_t_1418_: *mut crate::leanh::LeanObject,
    mut v_k_1419_: *mut crate::leanh::LeanObject,
    mut v_fallback_1420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1421_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0(v_00_u03b4_1417_, v_t_1418_, v_k_1419_, v_fallback_1420_);
    crate::leanh::lean_dec(v_fallback_1420_);
    crate::leanh::lean_dec(v_k_1419_);
    crate::leanh::lean_dec(v_t_1418_);
    return v_res_1421_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___lam__0(
    mut v___x_1422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1424_ = l_Lean_MessageData_toString(v___x_1422_);
    v___x_1425_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1425_, 0, v___x_1424_);
    return v___x_1425_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___lam__0___boxed(
    mut v___x_1426_: *mut crate::leanh::LeanObject,
    mut v___y_1427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1428_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___lam__0(v___x_1426_);
    return v_res_1428_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1429_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_1429_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1430_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0);
    v___x_1431_ = l_StateRefT_x27_instMonad___redArg(v___x_1430_);
    return v___x_1431_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12()
-> u64 {
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: u64 = 0;
    v___x_1451_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11;
    v___x_1452_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1451_);
    return v___x_1452_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1453_: u64 = 0;
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1453_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12);
    v___x_1454_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11;
    v___x_1455_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_1455_, 0, v___x_1454_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_1455_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1453_,
    );
    return v___x_1455_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1456_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1456_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1457_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14);
    v___x_1458_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1458_, 0, v___x_1457_);
    return v___x_1458_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1459_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1460_ = lean_mk_empty_array_with_capacity(v___x_1459_);
    v___x_1461_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1461_, 0, v___x_1460_);
    return v___x_1461_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1462_: usize = 0;
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1462_ = 5usize;
    v___x_1463_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1464_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1465_ = lean_mk_empty_array_with_capacity(v___x_1464_);
    v___x_1466_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16);
    v___x_1467_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1466_);
    crate::leanh::lean_ctor_set(v___x_1467_, 1, v___x_1465_);
    crate::leanh::lean_ctor_set(v___x_1467_, 2, v___x_1463_);
    crate::leanh::lean_ctor_set(v___x_1467_, 3, v___x_1463_);
    crate::leanh::lean_ctor_set_usize(v___x_1467_, 4, v___x_1462_);
    return v___x_1467_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1468_ = crate::leanh::lean_box(1);
    v___x_1469_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
    v___x_1470_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
    v___x_1471_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1471_, 0, v___x_1470_);
    crate::leanh::lean_ctor_set(v___x_1471_, 1, v___x_1469_);
    crate::leanh::lean_ctor_set(v___x_1471_, 2, v___x_1468_);
    return v___x_1471_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1474_: u8 = 0;
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: u8 = 0;
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1474_ = 1;
    v___x_1475_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1476_ = crate::leanh::lean_box(0);
    v___x_1477_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19;
    v___x_1478_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18);
    v___x_1479_ = crate::leanh::lean_box(1);
    v___x_1480_ = 0;
    v___x_1481_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13);
    v___x_1482_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
    crate::leanh::lean_ctor_set(v___x_1482_, 0, v___x_1481_);
    crate::leanh::lean_ctor_set(v___x_1482_, 1, v___x_1479_);
    crate::leanh::lean_ctor_set(v___x_1482_, 2, v___x_1478_);
    crate::leanh::lean_ctor_set(v___x_1482_, 3, v___x_1477_);
    crate::leanh::lean_ctor_set(v___x_1482_, 4, v___x_1476_);
    crate::leanh::lean_ctor_set(v___x_1482_, 5, v___x_1475_);
    crate::leanh::lean_ctor_set(v___x_1482_, 6, v___x_1476_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1482_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
        v___x_1480_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1482_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
        v___x_1480_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1482_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
        v___x_1480_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1482_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
        v___x_1474_,
    );
    return v___x_1482_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1483_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
    v___x_1484_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1485_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1485_, 0, v___x_1484_);
    crate::leanh::lean_ctor_set(v___x_1485_, 1, v___x_1484_);
    crate::leanh::lean_ctor_set(v___x_1485_, 2, v___x_1484_);
    crate::leanh::lean_ctor_set(v___x_1485_, 3, v___x_1484_);
    crate::leanh::lean_ctor_set(v___x_1485_, 4, v___x_1483_);
    crate::leanh::lean_ctor_set(v___x_1485_, 5, v___x_1483_);
    crate::leanh::lean_ctor_set(v___x_1485_, 6, v___x_1483_);
    crate::leanh::lean_ctor_set(v___x_1485_, 7, v___x_1483_);
    crate::leanh::lean_ctor_set(v___x_1485_, 8, v___x_1483_);
    crate::leanh::lean_ctor_set(v___x_1485_, 9, v___x_1483_);
    return v___x_1485_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1486_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
    v___x_1487_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1487_, 0, v___x_1486_);
    crate::leanh::lean_ctor_set(v___x_1487_, 1, v___x_1486_);
    crate::leanh::lean_ctor_set(v___x_1487_, 2, v___x_1486_);
    crate::leanh::lean_ctor_set(v___x_1487_, 3, v___x_1486_);
    crate::leanh::lean_ctor_set(v___x_1487_, 4, v___x_1486_);
    crate::leanh::lean_ctor_set(v___x_1487_, 5, v___x_1486_);
    return v___x_1487_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1488_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
    v___x_1489_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1489_, 0, v___x_1488_);
    crate::leanh::lean_ctor_set(v___x_1489_, 1, v___x_1488_);
    crate::leanh::lean_ctor_set(v___x_1489_, 2, v___x_1488_);
    crate::leanh::lean_ctor_set(v___x_1489_, 3, v___x_1488_);
    crate::leanh::lean_ctor_set(v___x_1489_, 4, v___x_1488_);
    return v___x_1489_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1490_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23);
    v___x_1491_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
    v___x_1492_ = crate::leanh::lean_box(1);
    v___x_1493_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22);
    v___x_1494_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21);
    v___x_1495_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1495_, 0, v___x_1494_);
    crate::leanh::lean_ctor_set(v___x_1495_, 1, v___x_1493_);
    crate::leanh::lean_ctor_set(v___x_1495_, 2, v___x_1492_);
    crate::leanh::lean_ctor_set(v___x_1495_, 3, v___x_1491_);
    crate::leanh::lean_ctor_set(v___x_1495_, 4, v___x_1490_);
    return v___x_1495_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: u8 = 0;
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2_once
        ),
        _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2,
    );
    v___x_1498_ = crate::leanh::lean_box(0);
    v___x_1499_ = 0;
    v___x_1500_ = l_Lean_firstFrontendMacroScope;
    v___x_1501_ = crate::leanh::lean_box(0);
    v___x_1502_ = crate::leanh::lean_box(0);
    v___x_1503_ = crate::leanh::lean_box(0);
    v___x_1504_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_1505_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1506_ = l_Lean_Options_empty;
    v___x_1507_ = l_Lean_instInhabitedFileMap_default;
    v___x_1508_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25;
    v___x_1509_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1509_, 0, v___x_1508_);
    crate::leanh::lean_ctor_set(v___x_1509_, 1, v___x_1507_);
    crate::leanh::lean_ctor_set(v___x_1509_, 2, v___x_1506_);
    crate::leanh::lean_ctor_set(v___x_1509_, 3, v___x_1505_);
    crate::leanh::lean_ctor_set(v___x_1509_, 4, v___x_1504_);
    crate::leanh::lean_ctor_set(v___x_1509_, 5, v___x_1503_);
    crate::leanh::lean_ctor_set(v___x_1509_, 6, v___x_1502_);
    crate::leanh::lean_ctor_set(v___x_1509_, 7, v___x_1501_);
    crate::leanh::lean_ctor_set(v___x_1509_, 8, v___x_1505_);
    crate::leanh::lean_ctor_set(v___x_1509_, 9, v___x_1505_);
    crate::leanh::lean_ctor_set(v___x_1509_, 10, v___x_1502_);
    crate::leanh::lean_ctor_set(v___x_1509_, 11, v___x_1500_);
    crate::leanh::lean_ctor_set(v___x_1509_, 12, v___x_1498_);
    crate::leanh::lean_ctor_set(v___x_1509_, 13, v___x_1497_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1509_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v___x_1499_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1509_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v___x_1499_,
    );
    return v___x_1509_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1510_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1511_ = l_Lean_firstFrontendMacroScope;
    v___x_1512_ = lean_nat_add(v___x_1511_, v___x_1510_);
    return v___x_1512_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: u64 = 0;
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1523_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
    v___x_1524_ = 0u64;
    v___x_1525_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_1525_, 0, v___x_1523_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_1525_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1524_,
    );
    return v___x_1525_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1526_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
    v___x_1527_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1527_, 0, v___x_1526_);
    crate::leanh::lean_ctor_set(v___x_1527_, 1, v___x_1526_);
    return v___x_1527_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = l_Lean_NameSet_empty;
    v___x_1529_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
    v___x_1530_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1530_, 0, v___x_1529_);
    crate::leanh::lean_ctor_set(v___x_1530_, 1, v___x_1529_);
    crate::leanh::lean_ctor_set(v___x_1530_, 2, v___x_1528_);
    return v___x_1530_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: u8 = 0;
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
    v___x_1532_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
    v___x_1533_ = 1;
    v___x_1534_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1534_, 0, v___x_1532_);
    crate::leanh::lean_ctor_set(v___x_1534_, 1, v___x_1532_);
    crate::leanh::lean_ctor_set(v___x_1534_, 2, v___x_1531_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1534_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1533_,
    );
    return v___x_1534_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(
    mut v_inst_1537_: *mut crate::leanh::LeanObject,
    mut v_env_1538_: *mut crate::leanh::LeanObject,
    mut v_x_1539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1560_: u8 = 0;
    let mut v_toFunctor_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1567_: u8 = 0;
    let mut v___f_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: u8 = 0;
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1619_: u8 = 0;
    let mut v_unused_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1621_: u8 = 0;
    let mut v_unused_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1540_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1);
                v_toApplicative_1541_ = crate::leanh::lean_ctor_get(v___x_1540_, 0);
                v_toFunctor_1542_ = crate::leanh::lean_ctor_get(v_toApplicative_1541_, 0);
                v_toSeq_1543_ = crate::leanh::lean_ctor_get(v_toApplicative_1541_, 2);
                v_toSeqLeft_1544_ = crate::leanh::lean_ctor_get(v_toApplicative_1541_, 3);
                v_toSeqRight_1545_ = crate::leanh::lean_ctor_get(v_toApplicative_1541_, 4);
                v___f_1546_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__2;
                v___f_1547_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_1542_, 2);
                v___f_1548_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1548_, 0, v_toFunctor_1542_);
                v___f_1549_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1549_, 0, v_toFunctor_1542_);
                v___x_1550_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1550_, 0, v___f_1548_);
                crate::leanh::lean_ctor_set(v___x_1550_, 1, v___f_1549_);
                crate::leanh::lean_inc(v_toSeqRight_1545_);
                v___f_1551_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1551_, 0, v_toSeqRight_1545_);
                crate::leanh::lean_inc(v_toSeqLeft_1544_);
                v___f_1552_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1552_, 0, v_toSeqLeft_1544_);
                crate::leanh::lean_inc(v_toSeq_1543_);
                v___f_1553_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1553_, 0, v_toSeq_1543_);
                v___x_1554_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1554_, 0, v___x_1550_);
                crate::leanh::lean_ctor_set(v___x_1554_, 1, v___f_1546_);
                crate::leanh::lean_ctor_set(v___x_1554_, 2, v___f_1553_);
                crate::leanh::lean_ctor_set(v___x_1554_, 3, v___f_1552_);
                crate::leanh::lean_ctor_set(v___x_1554_, 4, v___f_1551_);
                v___x_1555_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1555_, 0, v___x_1554_);
                crate::leanh::lean_ctor_set(v___x_1555_, 1, v___f_1547_);
                v___x_1556_ = l_StateRefT_x27_instMonad___redArg(v___x_1555_);
                v_toApplicative_1557_ = crate::leanh::lean_ctor_get(v___x_1556_, 0);
                v_isSharedCheck_1621_ = (!crate::leanh::lean_is_exclusive(v___x_1556_)) as u8;
                if v_isSharedCheck_1621_ == 0 {
                    v_unused_1622_ = crate::leanh::lean_ctor_get(v___x_1556_, 1);
                    crate::leanh::lean_dec(v_unused_1622_);
                    v___x_1559_ = v___x_1556_;
                    v_isShared_1560_ = v_isSharedCheck_1621_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1557_);
                    crate::leanh::lean_dec(v___x_1556_);
                    v___x_1559_ = crate::leanh::lean_box(0);
                    v_isShared_1560_ = v_isSharedCheck_1621_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1561_ = crate::leanh::lean_ctor_get(v_toApplicative_1557_, 0);
                v_toSeq_1562_ = crate::leanh::lean_ctor_get(v_toApplicative_1557_, 2);
                v_toSeqLeft_1563_ = crate::leanh::lean_ctor_get(v_toApplicative_1557_, 3);
                v_toSeqRight_1564_ = crate::leanh::lean_ctor_get(v_toApplicative_1557_, 4);
                v_isSharedCheck_1619_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1557_)) as u8;
                if v_isSharedCheck_1619_ == 0 {
                    v_unused_1620_ = crate::leanh::lean_ctor_get(v_toApplicative_1557_, 1);
                    crate::leanh::lean_dec(v_unused_1620_);
                    v___x_1566_ = v_toApplicative_1557_;
                    v_isShared_1567_ = v_isSharedCheck_1619_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1564_);
                    crate::leanh::lean_inc(v_toSeqLeft_1563_);
                    crate::leanh::lean_inc(v_toSeq_1562_);
                    crate::leanh::lean_inc(v_toFunctor_1561_);
                    crate::leanh::lean_dec(v_toApplicative_1557_);
                    v___x_1566_ = crate::leanh::lean_box(0);
                    v_isShared_1567_ = v_isSharedCheck_1619_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1568_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__4;
                v___f_1569_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_1561_);
                v___f_1570_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1570_, 0, v_toFunctor_1561_);
                v___f_1571_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1571_, 0, v_toFunctor_1561_);
                v___x_1572_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1572_, 0, v___f_1570_);
                crate::leanh::lean_ctor_set(v___x_1572_, 1, v___f_1571_);
                v___f_1573_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1573_, 0, v_toSeqRight_1564_);
                v___f_1574_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1574_, 0, v_toSeqLeft_1563_);
                v___f_1575_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1575_, 0, v_toSeq_1562_);
                if v_isShared_1567_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1566_, 4, v___f_1573_);
                    crate::leanh::lean_ctor_set(v___x_1566_, 3, v___f_1574_);
                    crate::leanh::lean_ctor_set(v___x_1566_, 2, v___f_1575_);
                    crate::leanh::lean_ctor_set(v___x_1566_, 1, v___f_1568_);
                    crate::leanh::lean_ctor_set(v___x_1566_, 0, v___x_1572_);
                    v___x_1577_ = v___x_1566_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1618_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1572_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 1, v___f_1568_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 2, v___f_1575_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 3, v___f_1574_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 4, v___f_1573_);
                    v___x_1577_ = v_reuseFailAlloc_1618_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1560_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1559_, 1, v___f_1569_);
                    crate::leanh::lean_ctor_set(v___x_1559_, 0, v___x_1577_);
                    v___x_1579_ = v___x_1559_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1617_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1577_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1617_, 1, v___f_1569_);
                    v___x_1579_ = v_reuseFailAlloc_1617_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1580_ = l_Lean_Meta_instMonadEnvMetaM;
                v___f_1581_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__10;
                v___x_1582_ = 1;
                v___x_1583_ = l_Lean_withoutExporting___redArg(
                    v___x_1579_,
                    v___x_1580_,
                    v___f_1581_,
                    v_x_1539_,
                    v___x_1582_,
                );
                v___x_1584_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19;
                v___x_1585_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20);
                v___x_1586_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24);
                v___x_1587_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_MetaM_run_x27___boxed as *mut core::ffi::c_void,
                    7,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_1587_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_1587_, 1, v___x_1583_);
                crate::leanh::lean_closure_set(v___x_1587_, 2, v___x_1585_);
                crate::leanh::lean_closure_set(v___x_1587_, 3, v___x_1586_);
                v___x_1588_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26);
                v___x_1589_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27);
                v___x_1590_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30;
                v___x_1591_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31;
                v___x_1592_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32);
                v___x_1593_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33);
                v___x_1594_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34);
                v___x_1595_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35);
                v___x_1596_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1596_, 0, v_env_1538_);
                crate::leanh::lean_ctor_set(v___x_1596_, 1, v___x_1589_);
                crate::leanh::lean_ctor_set(v___x_1596_, 2, v___x_1590_);
                crate::leanh::lean_ctor_set(v___x_1596_, 3, v___x_1591_);
                crate::leanh::lean_ctor_set(v___x_1596_, 4, v___x_1592_);
                crate::leanh::lean_ctor_set(v___x_1596_, 5, v___x_1593_);
                crate::leanh::lean_ctor_set(v___x_1596_, 6, v___x_1594_);
                crate::leanh::lean_ctor_set(v___x_1596_, 7, v___x_1595_);
                crate::leanh::lean_ctor_set(v___x_1596_, 8, v___x_1584_);
                v___x_1597_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Core_CoreM_run_x27___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_1597_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_1597_, 1, v___x_1587_);
                crate::leanh::lean_closure_set(v___x_1597_, 2, v___x_1588_);
                crate::leanh::lean_closure_set(v___x_1597_, 3, v___x_1596_);
                v___x_1598_ = crate::leanh::lean_alloc_closure(
                    l_EIO_toBaseIO___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_1598_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_1598_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_1598_, 2, v___x_1597_);
                v___x_1599_ = l_unsafeBaseIO___redArg(v___x_1598_);
                if crate::leanh::lean_obj_tag(v___x_1599_) == 0 {
                    v_a_1600_ = crate::leanh::lean_ctor_get(v___x_1599_, 0);
                    crate::leanh::lean_inc(v_a_1600_);
                    crate::leanh::lean_dec_ref_known(v___x_1599_, 1);
                    v___x_1601_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__36;
                    v___x_1602_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__37;
                    v___x_1603_ = crate::leanh::lean_unsigned_to_nat(75);
                    v___x_1604_ = crate::leanh::lean_unsigned_to_nat(24);
                    v___x_1609_ = l_Lean_Exception_toMessageData(v_a_1600_);
                    v___f_1610_ = crate::leanh::lean_alloc_closure(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_1610_, 0, v___x_1609_);
                    v___x_1611_ = crate::leanh::lean_alloc_closure(
                        l_EIO_toBaseIO___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_1611_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_1611_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_1611_, 2, v___f_1610_);
                    v___x_1612_ = l_unsafeBaseIO___redArg(v___x_1611_);
                    if crate::leanh::lean_obj_tag(v___x_1612_) == 0 {
                        v_a_1613_ = crate::leanh::lean_ctor_get(v___x_1612_, 0);
                        crate::leanh::lean_inc(v_a_1613_);
                        crate::leanh::lean_dec_ref_known(v___x_1612_, 1);
                        v___x_1614_ = lean_io_error_to_string(v_a_1613_);
                        v___y_1606_ = v___x_1614_;
                        state = 5;
                        continue;
                    } else {
                        v_a_1615_ = crate::leanh::lean_ctor_get(v___x_1612_, 0);
                        crate::leanh::lean_inc(v_a_1615_);
                        crate::leanh::lean_dec_ref_known(v___x_1612_, 1);
                        v___y_1606_ = v_a_1615_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_1616_ = crate::leanh::lean_ctor_get(v___x_1599_, 0);
                    crate::leanh::lean_inc(v_a_1616_);
                    crate::leanh::lean_dec_ref_known(v___x_1599_, 1);
                    return v_a_1616_;
                }
            }
            5 => {
                v___x_1607_ = l_mkPanicMessageWithDecl(
                    v___x_1601_,
                    v___x_1602_,
                    v___x_1603_,
                    v___x_1604_,
                    v___y_1606_,
                );
                crate::leanh::lean_dec_ref(v___y_1606_);
                v___x_1608_ = l_panic___redArg(v_inst_1537_, v___x_1607_);
                return v___x_1608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___boxed(
    mut v_inst_1623_: *mut crate::leanh::LeanObject,
    mut v_env_1624_: *mut crate::leanh::LeanObject,
    mut v_x_1625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1626_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(v_inst_1623_, v_env_1624_, v_x_1625_);
    crate::leanh::lean_dec(v_inst_1623_);
    return v_res_1626_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM(
    mut v_00_u03b1_1627_: *mut crate::leanh::LeanObject,
    mut v_inst_1628_: *mut crate::leanh::LeanObject,
    mut v_env_1629_: *mut crate::leanh::LeanObject,
    mut v_x_1630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1631_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(v_inst_1628_, v_env_1629_, v_x_1630_);
    return v___x_1631_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___boxed(
    mut v_00_u03b1_1632_: *mut crate::leanh::LeanObject,
    mut v_inst_1633_: *mut crate::leanh::LeanObject,
    mut v_env_1634_: *mut crate::leanh::LeanObject,
    mut v_x_1635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1636_ =
        l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM(
            v_00_u03b1_1632_,
            v_inst_1633_,
            v_env_1634_,
            v_x_1635_,
        );
    crate::leanh::lean_dec(v_inst_1633_);
    return v_res_1636_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0(
    mut v___y_1637_: *mut crate::leanh::LeanObject,
    mut v___y_1638_: *mut crate::leanh::LeanObject,
    mut v___y_1639_: *mut crate::leanh::LeanObject,
    mut v___y_1640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1646_: u8 = 0;
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1653_: u8 = 0;
    let mut v_a_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1657_: u8 = 0;
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1661_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1642_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap(v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
                if crate::leanh::lean_obj_tag(v___x_1642_) == 0 {
                    v_a_1643_ = crate::leanh::lean_ctor_get(v___x_1642_, 0);
                    v_isSharedCheck_1653_ = (!crate::leanh::lean_is_exclusive(v___x_1642_)) as u8;
                    if v_isSharedCheck_1653_ == 0 {
                        v___x_1645_ = v___x_1642_;
                        v_isShared_1646_ = v_isSharedCheck_1653_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1643_);
                        crate::leanh::lean_dec(v___x_1642_);
                        v___x_1645_ = crate::leanh::lean_box(0);
                        v_isShared_1646_ = v_isSharedCheck_1653_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1654_ = crate::leanh::lean_ctor_get(v___x_1642_, 0);
                    v_isSharedCheck_1661_ = (!crate::leanh::lean_is_exclusive(v___x_1642_)) as u8;
                    if v_isSharedCheck_1661_ == 0 {
                        v___x_1656_ = v___x_1642_;
                        v_isShared_1657_ = v_isSharedCheck_1661_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1654_);
                        crate::leanh::lean_dec(v___x_1642_);
                        v___x_1656_ = crate::leanh::lean_box(0);
                        v_isShared_1657_ = v_isSharedCheck_1661_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1647_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1648_ = lean_mk_empty_array_with_capacity(v___x_1647_);
                v___x_1649_ = lean_array_push(v___x_1648_, v_a_1643_);
                if v_isShared_1646_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1645_, 0, v___x_1649_);
                    v___x_1651_ = v___x_1645_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1652_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
                    v___x_1651_ = v_reuseFailAlloc_1652_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1651_;
            }
            3 => {
                if v_isShared_1657_ == 0 {
                    v___x_1659_ = v___x_1656_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1660_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
                    v___x_1659_ = v_reuseFailAlloc_1660_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0___boxed(
    mut v___y_1662_: *mut crate::leanh::LeanObject,
    mut v___y_1663_: *mut crate::leanh::LeanObject,
    mut v___y_1664_: *mut crate::leanh::LeanObject,
    mut v___y_1665_: *mut crate::leanh::LeanObject,
    mut v___y_1666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1667_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0(v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
    crate::leanh::lean_dec(v___y_1665_);
    crate::leanh::lean_dec_ref(v___y_1664_);
    crate::leanh::lean_dec(v___y_1663_);
    crate::leanh::lean_dec_ref(v___y_1662_);
    return v_res_1667_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1669_ = l_Array_instInhabited(crate::leanh::lean_box(0));
    return v___x_1669_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3(
    mut v_env_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ents_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1671_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__0;
    v___x_1672_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1);
    v_ents_1673_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(v___x_1672_, v_env_1670_, v___f_1671_);
    crate::leanh::lean_inc_n(v_ents_1673_, 2);
    v___x_1674_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1674_, 0, v_ents_1673_);
    crate::leanh::lean_ctor_set(v___x_1674_, 1, v_ents_1673_);
    crate::leanh::lean_ctor_set(v___x_1674_, 2, v_ents_1673_);
    return v___x_1674_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(
    mut v_x_1677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1678_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_;
    return v___x_1678_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(
    mut v_x_1679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1680_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v_x_1679_);
    crate::leanh::lean_dec_ref(v_x_1679_);
    return v_res_1680_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(
    mut v_x_1684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1685_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_;
    return v___x_1685_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(
    mut v_x_1686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1687_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v_x_1686_);
    crate::leanh::lean_dec_ref(v_x_1686_);
    return v_res_1687_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(
    mut v_env_1688_: *mut crate::leanh::LeanObject,
    mut v_x_1689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1690_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3(v_env_1688_);
    return v___x_1690_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(
    mut v_env_1691_: *mut crate::leanh::LeanObject,
    mut v_x_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1693_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v_env_1691_, v_x_1692_);
    crate::leanh::lean_dec_ref(v_x_1692_);
    return v_res_1693_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(
    mut v_a_1694_: *mut crate::leanh::LeanObject,
    mut v_a_1695_: u8,
) -> *mut crate::leanh::LeanObject {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(
    mut v_a_1696_: *mut crate::leanh::LeanObject,
    mut v_a_1697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_110__boxed_1698_: u8 = 0;
    let mut v_res_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_110__boxed_1698_ = (crate::leanh::lean_unbox(v_a_1697_) as u8);
    v_res_1699_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v_a_1696_, v_a_110__boxed_1698_);
    crate::leanh::lean_dec_ref(v_a_1696_);
    return v_res_1699_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(
    mut v_mapss_1700_: *mut crate::leanh::LeanObject,
    mut v_x_1701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1703_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1703_, 0, v_mapss_1700_);
    return v___x_1703_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(
    mut v_mapss_1704_: *mut crate::leanh::LeanObject,
    mut v_x_1705_: *mut crate::leanh::LeanObject,
    mut v___y_1706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1707_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v_mapss_1704_, v_x_1705_);
    crate::leanh::lean_dec_ref(v_x_1705_);
    return v_res_1707_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(
    mut v___x_1708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1710_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1710_, 0, v___x_1708_);
    return v___x_1710_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(
    mut v___x_1711_: *mut crate::leanh::LeanObject,
    mut v___y_1712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1713_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v___x_1711_);
    return v_res_1713_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1738_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_;
    v___x_1739_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1738_);
    return v___x_1739_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(
    mut v_a_1740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1741_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_();
    return v_res_1741_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1743_ = crate::leanh::lean_box(0);
    v___x_1744_ = lean_st_mk_ref(v___x_1743_);
    v___x_1745_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1745_, 0, v___x_1744_);
    return v___x_1745_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2____boxed(
    mut v_a_1746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1747_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2_();
    return v_res_1747_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instZeroNameMapNat()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1748_ = crate::leanh::lean_box(1);
    return v___x_1748_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0(
    mut v___x_1749_: *mut crate::leanh::LeanObject,
    mut v_x_x27_1750_: *mut crate::leanh::LeanObject,
    mut v_n_1751_: *mut crate::leanh::LeanObject,
    mut v_c_1752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1753_ = crate::leanh::lean_unsigned_to_nat(0);
    crate::leanh::lean_inc(v_n_1751_);
    crate::leanh::lean_inc(v_x_x27_1750_);
    v___x_1754_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(
        v___x_1749_,
        v_x_x27_1750_,
        v_n_1751_,
        v___x_1753_,
    );
    v___x_1755_ = lean_nat_add(v___x_1754_, v_c_1752_);
    crate::leanh::lean_dec(v___x_1754_);
    v___x_1756_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_n_1751_,
        v___x_1755_,
        v_x_x27_1750_,
    );
    return v___x_1756_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0___boxed(
    mut v___x_1757_: *mut crate::leanh::LeanObject,
    mut v_x_x27_1758_: *mut crate::leanh::LeanObject,
    mut v_n_1759_: *mut crate::leanh::LeanObject,
    mut v_c_1760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1761_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0(v___x_1757_, v_x_x27_1758_, v_n_1759_, v_c_1760_);
    crate::leanh::lean_dec(v_c_1760_);
    return v_res_1761_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1(
    mut v_x_1765_: *mut crate::leanh::LeanObject,
    mut v_y_1766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1767_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__1;
    v___x_1768_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1767_, v_x_1765_, v_y_1766_);
    return v___x_1768_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(
    mut v_init_1771_: *mut crate::leanh::LeanObject,
    mut v_x_1772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1772_) == 0 {
                    v_k_1773_ = crate::leanh::lean_ctor_get(v_x_1772_, 1);
                    crate::leanh::lean_inc(v_k_1773_);
                    v_v_1774_ = crate::leanh::lean_ctor_get(v_x_1772_, 2);
                    crate::leanh::lean_inc(v_v_1774_);
                    v_l_1775_ = crate::leanh::lean_ctor_get(v_x_1772_, 3);
                    crate::leanh::lean_inc(v_l_1775_);
                    v_r_1776_ = crate::leanh::lean_ctor_get(v_x_1772_, 4);
                    crate::leanh::lean_inc(v_r_1776_);
                    crate::leanh::lean_dec_ref_known(v_x_1772_, 5);
                    v___x_1777_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(v_init_1771_, v_l_1775_);
                    v___x_1778_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1779_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v___x_1777_, v_k_1773_, v___x_1778_);
                    v___x_1780_ = lean_nat_add(v___x_1779_, v_v_1774_);
                    crate::leanh::lean_dec(v_v_1774_);
                    crate::leanh::lean_dec(v___x_1779_);
                    v___x_1781_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1773_, v___x_1780_, v___x_1777_);
                    v_init_1771_ = v___x_1781_;
                    v_x_1772_ = v_r_1776_;
                    state = 0;
                    continue;
                } else {
                    return v_init_1771_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(
    mut v_as_1783_: *mut crate::leanh::LeanObject,
    mut v_i_1784_: usize,
    mut v_stop_1785_: usize,
    mut v_b_1786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1787_: u8 = 0;
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: usize = 0;
    let mut v___x_1791_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1787_ = lean_usize_dec_eq(v_i_1784_, v_stop_1785_);
                if v___x_1787_ == 0 {
                    v___x_1788_ = lean_array_uget_borrowed(v_as_1783_, v_i_1784_);
                    crate::leanh::lean_inc(v___x_1788_);
                    v___x_1789_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(v_b_1786_, v___x_1788_);
                    v___x_1790_ = 1usize;
                    v___x_1791_ = lean_usize_add(v_i_1784_, v___x_1790_);
                    v_i_1784_ = v___x_1791_;
                    v_b_1786_ = v___x_1789_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1786_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___boxed(
    mut v_as_1793_: *mut crate::leanh::LeanObject,
    mut v_i_1794_: *mut crate::leanh::LeanObject,
    mut v_stop_1795_: *mut crate::leanh::LeanObject,
    mut v_b_1796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1797_: usize = 0;
    let mut v_stop_boxed_1798_: usize = 0;
    let mut v_res_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1797_ = crate::leanh::lean_unbox_usize(v_i_1794_);
    crate::leanh::lean_dec(v_i_1794_);
    v_stop_boxed_1798_ = crate::leanh::lean_unbox_usize(v_stop_1795_);
    crate::leanh::lean_dec(v_stop_1795_);
    v_res_1799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(v_as_1793_, v_i_boxed_1797_, v_stop_boxed_1798_, v_b_1796_);
    crate::leanh::lean_dec_ref(v_as_1793_);
    return v_res_1799_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(
    mut v_as_1800_: *mut crate::leanh::LeanObject,
    mut v_i_1801_: usize,
    mut v_stop_1802_: usize,
    mut v_b_1803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: usize = 0;
    let mut v___x_1807_: usize = 0;
    let mut v___x_1809_: u8 = 0;
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: u8 = 0;
    let mut v___x_1814_: u8 = 0;
    let mut v___x_1815_: usize = 0;
    let mut v___x_1816_: usize = 0;
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: usize = 0;
    let mut v___x_1819_: usize = 0;
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1809_ = lean_usize_dec_eq(v_i_1801_, v_stop_1802_);
                if v___x_1809_ == 0 {
                    v___x_1810_ = lean_array_uget_borrowed(v_as_1800_, v_i_1801_);
                    v___x_1811_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1812_ = lean_array_get_size(v___x_1810_);
                    v___x_1813_ = lean_nat_dec_lt(v___x_1811_, v___x_1812_);
                    if v___x_1813_ == 0 {
                        v___y_1805_ = v_b_1803_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1814_ = lean_nat_dec_le(v___x_1812_, v___x_1812_);
                        if v___x_1814_ == 0 {
                            if v___x_1813_ == 0 {
                                v___y_1805_ = v_b_1803_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1815_ = 0usize;
                                v___x_1816_ = lean_usize_of_nat(v___x_1812_);
                                v___x_1817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(v___x_1810_, v___x_1815_, v___x_1816_, v_b_1803_);
                                v___y_1805_ = v___x_1817_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_1818_ = 0usize;
                            v___x_1819_ = lean_usize_of_nat(v___x_1812_);
                            v___x_1820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(v___x_1810_, v___x_1818_, v___x_1819_, v_b_1803_);
                            v___y_1805_ = v___x_1820_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_1803_;
                }
            }
            1 => {
                v___x_1806_ = 1usize;
                v___x_1807_ = lean_usize_add(v_i_1801_, v___x_1806_);
                v_i_1801_ = v___x_1807_;
                v_b_1803_ = v___y_1805_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2___boxed(
    mut v_as_1821_: *mut crate::leanh::LeanObject,
    mut v_i_1822_: *mut crate::leanh::LeanObject,
    mut v_stop_1823_: *mut crate::leanh::LeanObject,
    mut v_b_1824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1825_: usize = 0;
    let mut v_stop_boxed_1826_: usize = 0;
    let mut v_res_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1825_ = crate::leanh::lean_unbox_usize(v_i_1822_);
    crate::leanh::lean_dec(v_i_1822_);
    v_stop_boxed_1826_ = crate::leanh::lean_unbox_usize(v_stop_1823_);
    crate::leanh::lean_dec(v_stop_1823_);
    v_res_1827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(v_as_1821_, v_i_boxed_1825_, v_stop_boxed_1826_, v_b_1824_);
    crate::leanh::lean_dec_ref(v_as_1821_);
    return v_res_1827_;
}
pub unsafe fn _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1828_ = l_Array_instInhabited(crate::leanh::lean_box(0));
    return v___x_1828_;
}
pub unsafe fn l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(
    mut v_a_1829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: u8 = 0;
    let mut v___x_1850_: u8 = 0;
    let mut v___x_1851_: usize = 0;
    let mut v___x_1852_: usize = 0;
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: usize = 0;
    let mut v___x_1855_: usize = 0;
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1860_: u8 = 0;
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1864_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1831_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyMapRef;
                v___x_1832_ = lean_st_ref_get(v___x_1831_);
                if crate::leanh::lean_obj_tag(v___x_1832_) == 0 {
                    v___x_1833_ = lean_st_ref_get(v_a_1829_);
                    v_env_1839_ = crate::leanh::lean_ctor_get(v___x_1833_, 0);
                    crate::leanh::lean_inc_ref(v_env_1839_);
                    crate::leanh::lean_dec(v___x_1833_);
                    v___x_1840_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt;
                    v_toEnvExtension_1841_ = crate::leanh::lean_ctor_get(v___x_1840_, 0);
                    v_asyncMode_1842_ = crate::leanh::lean_ctor_get(v_toEnvExtension_1841_, 2);
                    v___x_1843_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0_once
                        ),
                        _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0,
                    );
                    v___x_1844_ = crate::leanh::lean_box(0);
                    v___x_1845_ = l_Lean_PersistentEnvExtension_getState___redArg(
                        v___x_1843_,
                        v___x_1840_,
                        v_env_1839_,
                        v_asyncMode_1842_,
                        v___x_1844_,
                    );
                    v___x_1846_ = crate::leanh::lean_box(1);
                    v___x_1847_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1848_ = lean_array_get_size(v___x_1845_);
                    v___x_1849_ = lean_nat_dec_lt(v___x_1847_, v___x_1848_);
                    if v___x_1849_ == 0 {
                        crate::leanh::lean_dec(v___x_1845_);
                        v___y_1835_ = v___x_1846_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1850_ = lean_nat_dec_le(v___x_1848_, v___x_1848_);
                        if v___x_1850_ == 0 {
                            if v___x_1849_ == 0 {
                                crate::leanh::lean_dec(v___x_1845_);
                                v___y_1835_ = v___x_1846_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1851_ = 0usize;
                                v___x_1852_ = lean_usize_of_nat(v___x_1848_);
                                v___x_1853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(v___x_1845_, v___x_1851_, v___x_1852_, v___x_1846_);
                                crate::leanh::lean_dec(v___x_1845_);
                                v___y_1835_ = v___x_1853_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_1854_ = 0usize;
                            v___x_1855_ = lean_usize_of_nat(v___x_1848_);
                            v___x_1856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(v___x_1845_, v___x_1854_, v___x_1855_, v___x_1846_);
                            crate::leanh::lean_dec(v___x_1845_);
                            v___y_1835_ = v___x_1856_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_val_1857_ = crate::leanh::lean_ctor_get(v___x_1832_, 0);
                    v_isSharedCheck_1864_ = (!crate::leanh::lean_is_exclusive(v___x_1832_)) as u8;
                    if v_isSharedCheck_1864_ == 0 {
                        v___x_1859_ = v___x_1832_;
                        v_isShared_1860_ = v_isSharedCheck_1864_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1857_);
                        crate::leanh::lean_dec(v___x_1832_);
                        v___x_1859_ = crate::leanh::lean_box(0);
                        v_isShared_1860_ = v_isSharedCheck_1864_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_1835_);
                v___x_1836_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1836_, 0, v___y_1835_);
                v___x_1837_ = lean_st_ref_set(v___x_1831_, v___x_1836_);
                v___x_1838_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1838_, 0, v___y_1835_);
                return v___x_1838_;
            }
            2 => {
                if v_isShared_1860_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1859_, 0);
                    v___x_1862_ = v___x_1859_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1863_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_val_1857_);
                    v___x_1862_ = v_reuseFailAlloc_1863_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1862_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___boxed(
    mut v_a_1865_: *mut crate::leanh::LeanObject,
    mut v_a_1866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1867_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(v_a_1865_);
    crate::leanh::lean_dec(v_a_1865_);
    return v_res_1867_;
}
pub unsafe fn l_Lean_LibrarySuggestions_symbolFrequencyMap(
    mut v_a_1868_: *mut crate::leanh::LeanObject,
    mut v_a_1869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1871_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(v_a_1869_);
    return v___x_1871_;
}
pub unsafe fn l_Lean_LibrarySuggestions_symbolFrequencyMap___boxed(
    mut v_a_1872_: *mut crate::leanh::LeanObject,
    mut v_a_1873_: *mut crate::leanh::LeanObject,
    mut v_a_1874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1875_ = l_Lean_LibrarySuggestions_symbolFrequencyMap(v_a_1872_, v_a_1873_);
    crate::leanh::lean_dec(v_a_1873_);
    crate::leanh::lean_dec_ref(v_a_1872_);
    return v_res_1875_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0(
    mut v_init_1876_: *mut crate::leanh::LeanObject,
    mut v_t_1877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1878_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(v_init_1876_, v_t_1877_);
    return v___x_1878_;
}
pub unsafe fn l_Lean_LibrarySuggestions_symbolFrequency___redArg(
    mut v_n_1879_: *mut crate::leanh::LeanObject,
    mut v_a_1880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1886_: u8 = 0;
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1892_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1882_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(v_a_1880_);
                v_a_1883_ = crate::leanh::lean_ctor_get(v___x_1882_, 0);
                v_isSharedCheck_1892_ = (!crate::leanh::lean_is_exclusive(v___x_1882_)) as u8;
                if v_isSharedCheck_1892_ == 0 {
                    v___x_1885_ = v___x_1882_;
                    v_isShared_1886_ = v_isSharedCheck_1892_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1883_);
                    crate::leanh::lean_dec(v___x_1882_);
                    v___x_1885_ = crate::leanh::lean_box(0);
                    v_isShared_1886_ = v_isSharedCheck_1892_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1887_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1888_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_a_1883_, v_n_1879_, v___x_1887_);
                crate::leanh::lean_dec(v_a_1883_);
                if v_isShared_1886_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1885_, 0, v___x_1888_);
                    v___x_1890_ = v___x_1885_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1891_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
                    v___x_1890_ = v_reuseFailAlloc_1891_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1890_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_LibrarySuggestions_symbolFrequency___redArg___boxed(
    mut v_n_1893_: *mut crate::leanh::LeanObject,
    mut v_a_1894_: *mut crate::leanh::LeanObject,
    mut v_a_1895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1896_ = l_Lean_LibrarySuggestions_symbolFrequency___redArg(v_n_1893_, v_a_1894_);
    crate::leanh::lean_dec(v_a_1894_);
    crate::leanh::lean_dec(v_n_1893_);
    return v_res_1896_;
}
pub unsafe fn l_Lean_LibrarySuggestions_symbolFrequency(
    mut v_n_1897_: *mut crate::leanh::LeanObject,
    mut v_a_1898_: *mut crate::leanh::LeanObject,
    mut v_a_1899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1901_ = l_Lean_LibrarySuggestions_symbolFrequency___redArg(v_n_1897_, v_a_1899_);
    return v___x_1901_;
}
pub unsafe fn l_Lean_LibrarySuggestions_symbolFrequency___boxed(
    mut v_n_1902_: *mut crate::leanh::LeanObject,
    mut v_a_1903_: *mut crate::leanh::LeanObject,
    mut v_a_1904_: *mut crate::leanh::LeanObject,
    mut v_a_1905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1906_ = l_Lean_LibrarySuggestions_symbolFrequency(v_n_1902_, v_a_1903_, v_a_1904_);
    crate::leanh::lean_dec(v_a_1904_);
    crate::leanh::lean_dec_ref(v_a_1903_);
    crate::leanh::lean_dec(v_n_1902_);
    return v_res_1906_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_LibrarySuggestions_SymbolFrequency(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_LibrarySuggestions_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_localSymbolFrequencyMapRef = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_localSymbolFrequencyMapRef);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyMapRef = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyMapRef);
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instZeroNameMapNat = _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instZeroNameMapNat();
    crate::leanh::lean_mark_persistent(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instZeroNameMapNat);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_LibrarySuggestions_SymbolFrequency(
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
pub unsafe fn initialize_Lean_LibrarySuggestions_SymbolFrequency(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_LibrarySuggestions_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
}

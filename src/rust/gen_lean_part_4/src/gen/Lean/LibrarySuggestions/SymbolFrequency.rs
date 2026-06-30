// Lean compiler output
// Module: Lean.LibrarySuggestions.SymbolFrequency
// Imports: Lean.Meta.Basic Lean.LibrarySuggestions.Basic
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_array_uget_borrowed,
    lean_mk_array, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_le,
    lean_nat_dec_lt, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_usize_add,
    lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Reader::l_ReaderT_tryFinally___redArg___lam__1;
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_instMonad___redArg, l_instMonadFinallyStateRefT_x27___aux__1___boxed,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_instInhabited;
use crate::r#gen::Init::Prelude::{
    l_Lean_firstFrontendMacroScope, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
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
static mut l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_LibrarySuggestions_localSymbolFrequencyMap___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LibrarySuggestions_localSymbolFrequencyMap___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_localSymbolFrequencyMapRef: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__6_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_instMonadFinallyEIO___aux__1___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__7_value: leanh::LeanClosureObject<4> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*4) as u16, other: 0, tag: 245 }, m_fun: l_instMonadFinallyStateRefT_x27___aux__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 4, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__6_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__8_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_ReaderT_tryFinally___redArg___lam__1 as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__7_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__9_value: leanh::LeanClosureObject<4> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*4) as u16, other: 0, tag: 245 }, m_fun: l_instMonadFinallyStateRefT_x27___aux__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 4, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__8_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__10_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_ReaderT_tryFinally___redArg___lam__1 as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__9_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*0 + 24) as u16, other: 0, tag: 0 }, m_objs: [282574488338432 as *mut leanh::LeanObject,72621647814721793 as *mut leanh::LeanObject,65793 as *mut leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11_value) as *mut leanh::LeanObject;
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12: u64 = 0;
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19_value) as *mut leanh::LeanObject;
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [115, 121, 109, 98, 111, 108, 70, 114, 101, 113, 117, 101, 110, 99, 121, 0]};
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25_value) as *mut leanh::LeanObject;
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [95, 117, 110, 105, 113, 0]};
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28_value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__28_value) as *mut leanh::LeanObject,3978731030111751661 as *mut leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29_value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__29_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30_value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31_value) as *mut leanh::LeanObject;
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__36_value: leanh::LeanStringObject<40> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [76, 101, 97, 110, 46, 76, 105, 98, 114, 97, 114, 121, 83, 117, 103, 103, 101, 115, 116, 105, 111, 110, 115, 46, 83, 121, 109, 98, 111, 108, 70, 114, 101, 113, 117, 101, 110, 99, 121, 0]};
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__36: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__36_value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__37_value: leanh::LeanStringObject<83> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 83, m_capacity: 83, m_length: 82, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 76, 105, 98, 114, 97, 114, 121, 83, 117, 103, 103, 101, 115, 116, 105, 111, 110, 115, 46, 83, 121, 109, 98, 111, 108, 70, 114, 101, 113, 117, 101, 110, 99, 121, 46, 48, 46, 76, 101, 97, 110, 46, 69, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 46, 117, 110, 115, 97, 102, 101, 82, 117, 110, 77, 101, 116, 97, 77, 0]};
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__37: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__37_value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [115, 121, 109, 98, 111, 108, 32, 102, 114, 101, 113, 117, 101, 110, 99, 121, 32, 101, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25_value) as *mut leanh::LeanObject,4785150241512038666 as *mut leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: leanh::LeanCtorObject<8> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*8 + 0) as u16, other: 8, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyMapRef: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instZeroNameMapNat: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__1_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___lam__0(
    mut v_i_x3f_954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_i_x3f_954_) == 0 {
                    v___x_960_ = leanh::lean_unsigned_to_nat(0);
                    v___y_956_ = v___x_960_;
                    state = 1;
                    continue;
                } else {
                    v_val_961_ = leanh::lean_ctor_get(v_i_x3f_954_, 0);
                    v___y_956_ = v_val_961_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_957_ = leanh::lean_unsigned_to_nat(1);
                v___x_958_ = lean_nat_add(v___y_956_, v___x_957_);
                v___x_959_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_959_, 0, v___x_958_);
                return v___x_959_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___lam__0___boxed(
    mut v_i_x3f_962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_963_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___lam__0(v_i_x3f_962_);
    leanh::lean_dec(v_i_x3f_962_);
    return v_res_963_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_964_ = leanh::lean_box(0);
    v___x_965_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___lam__0(v___x_964_);
    return v___x_965_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg(
    mut v_k_966_: *mut leanh::LeanObject,
    mut v_t_967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_975_: u8 = 0;
    let mut v___x_976_: u8 = 0;
    let mut v_impl_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_987_: u8 = 0;
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_967_) == 0 {
                    v_size_968_ = leanh::lean_ctor_get(v_t_967_, 0);
                    v_k_969_ = leanh::lean_ctor_get(v_t_967_, 1);
                    v_v_970_ = leanh::lean_ctor_get(v_t_967_, 2);
                    v_l_971_ = leanh::lean_ctor_get(v_t_967_, 3);
                    v_r_972_ = leanh::lean_ctor_get(v_t_967_, 4);
                    v_isSharedCheck_987_ = (!leanh::lean_is_exclusive(v_t_967_)) as u8;
                    if v_isSharedCheck_987_ == 0 {
                        v___x_974_ = v_t_967_;
                        v_isShared_975_ = v_isSharedCheck_987_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_972_);
                        leanh::lean_inc(v_l_971_);
                        leanh::lean_inc(v_v_970_);
                        leanh::lean_inc(v_k_969_);
                        leanh::lean_inc(v_size_968_);
                        leanh::lean_dec(v_t_967_);
                        v___x_974_ = leanh::lean_box(0);
                        v_isShared_975_ = v_isSharedCheck_987_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_988_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___closed__0_once), _init_l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___closed__0);
                    v_val_989_ = leanh::lean_ctor_get(v___x_988_, 0);
                    v___x_990_ = leanh::lean_unsigned_to_nat(1);
                    leanh::lean_inc(v_val_989_);
                    v___x_991_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_991_, 0, v___x_990_);
                    leanh::lean_ctor_set(v___x_991_, 1, v_k_966_);
                    leanh::lean_ctor_set(v___x_991_, 2, v_val_989_);
                    leanh::lean_ctor_set(v___x_991_, 3, v_t_967_);
                    leanh::lean_ctor_set(v___x_991_, 4, v_t_967_);
                    return v___x_991_;
                }
            }
            1 => {
                v___x_976_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_966_, v_k_969_);
                match v___x_976_ {
                    0 => {
                        leanh::lean_del_object(v___x_974_);
                        leanh::lean_dec(v_size_968_);
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
                        leanh::lean_dec(v_k_969_);
                        v___x_979_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_979_, 0, v_v_970_);
                        v___x_980_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg___lam__0(v___x_979_);
                        leanh::lean_dec_ref_known(v___x_979_, 1);
                        v_val_981_ = leanh::lean_ctor_get(v___x_980_, 0);
                        leanh::lean_inc(v_val_981_);
                        leanh::lean_dec(v___x_980_);
                        if v_isShared_975_ == 0 {
                            leanh::lean_ctor_set(v___x_974_, 2, v_val_981_);
                            leanh::lean_ctor_set(v___x_974_, 1, v_k_966_);
                            v___x_983_ = v___x_974_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_984_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_984_, 0, v_size_968_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_984_, 1, v_k_966_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_984_, 2, v_val_981_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_984_, 3, v_l_971_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_984_, 4, v_r_972_);
                            v___x_983_ = v_reuseFailAlloc_984_;
                            state = 2;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_del_object(v___x_974_);
                        leanh::lean_dec(v_size_968_);
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
    mut v_n_x27_992_: *mut leanh::LeanObject,
    mut v_acc_993_: *mut leanh::LeanObject,
    mut v___y_994_: *mut leanh::LeanObject,
    mut v___y_995_: *mut leanh::LeanObject,
    mut v___y_996_: *mut leanh::LeanObject,
    mut v___y_997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_999_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg(v_n_x27_992_, v_acc_993_);
    v___x_1000_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1000_, 0, v___x_999_);
    return v___x_1000_;
}
pub unsafe fn l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__0___boxed(
    mut v_n_x27_1001_: *mut leanh::LeanObject,
    mut v_acc_1002_: *mut leanh::LeanObject,
    mut v___y_1003_: *mut leanh::LeanObject,
    mut v___y_1004_: *mut leanh::LeanObject,
    mut v___y_1005_: *mut leanh::LeanObject,
    mut v___y_1006_: *mut leanh::LeanObject,
    mut v___y_1007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1008_ = l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__0(
        v_n_x27_1001_,
        v_acc_1002_,
        v___y_1003_,
        v___y_1004_,
        v___y_1005_,
        v___y_1006_,
    );
    leanh::lean_dec(v___y_1006_);
    leanh::lean_dec_ref(v___y_1005_);
    leanh::lean_dec(v___y_1004_);
    leanh::lean_dec_ref(v___y_1003_);
    return v_res_1008_;
}
pub unsafe fn _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1009_ = leanh::lean_unsigned_to_nat(64);
    v___x_1010_ = l_Lean_mkPtrSet___redArg(v___x_1009_);
    return v___x_1010_;
}
pub unsafe fn _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1011_ = leanh::lean_box(0);
    v___x_1012_ = leanh::lean_unsigned_to_nat(16);
    v___x_1013_ = lean_mk_array(v___x_1012_, v___x_1011_);
    return v___x_1013_;
}
pub unsafe fn _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1014_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__1_once
        ),
        _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__1,
    );
    v___x_1015_ = leanh::lean_unsigned_to_nat(0);
    v___x_1016_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1016_, 0, v___x_1015_);
    leanh::lean_ctor_set(v___x_1016_, 1, v___x_1014_);
    return v___x_1016_;
}
pub unsafe fn _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1017_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2_once
        ),
        _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2,
    );
    v___x_1018_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__0_once
        ),
        _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__0,
    );
    v___x_1019_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1019_, 0, v___x_1018_);
    leanh::lean_ctor_set(v___x_1019_, 1, v___x_1017_);
    return v___x_1019_;
}
pub unsafe fn l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1(
    mut v___f_1020_: *mut leanh::LeanObject,
    mut v_env_1021_: *mut leanh::LeanObject,
    mut v_acc_1022_: *mut leanh::LeanObject,
    mut v_m_1023_: *mut leanh::LeanObject,
    mut v_ci_1024_: *mut leanh::LeanObject,
    mut v___y_1025_: *mut leanh::LeanObject,
    mut v___y_1026_: *mut leanh::LeanObject,
    mut v___y_1027_: *mut leanh::LeanObject,
    mut v___y_1028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1031_: u8 = 0;
    let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1038_: u8 = 0;
    let mut v_fst_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1043_: u8 = 0;
    let mut v_a_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1047_: u8 = 0;
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1051_: u8 = 0;
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: u8 = 0;
    let mut v___x_1054_: u8 = 0;
    let mut v___x_1055_: u8 = 0;
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1053_ = 0;
                leanh::lean_inc(v_m_1023_);
                leanh::lean_inc_ref(v_env_1021_);
                v___x_1054_ =
                    l_Lean_LibrarySuggestions_isDeniedPremise(v_env_1021_, v_m_1023_, v___x_1053_);
                if v___x_1054_ == 0 {
                    v___x_1055_ = l_Lean_wasOriginallyTheorem(v_env_1021_, v_m_1023_);
                    if v___x_1055_ == 0 {
                        leanh::lean_dec_ref(v___f_1020_);
                        v___x_1056_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1056_, 0, v_acc_1022_);
                        return v___x_1056_;
                    } else {
                        v___y_1031_ = v___x_1054_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_m_1023_);
                    leanh::lean_dec_ref(v_env_1021_);
                    v___y_1031_ = v___x_1054_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1031_ == 0 {
                    v___x_1032_ = l_Lean_ConstantInfo_type(v_ci_1024_);
                    v___x_1033_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__3), core::ptr::addr_of_mut!(l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__3_once), _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__3);
                    v___x_1034_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit(leanh::lean_box(0), v___f_1020_, v___x_1032_, v_acc_1022_, v___x_1033_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
                    if leanh::lean_obj_tag(v___x_1034_) == 0 {
                        v_a_1035_ = leanh::lean_ctor_get(v___x_1034_, 0);
                        v_isSharedCheck_1043_ =
                            (!leanh::lean_is_exclusive(v___x_1034_)) as u8;
                        if v_isSharedCheck_1043_ == 0 {
                            v___x_1037_ = v___x_1034_;
                            v_isShared_1038_ = v_isSharedCheck_1043_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1035_);
                            leanh::lean_dec(v___x_1034_);
                            v___x_1037_ = leanh::lean_box(0);
                            v_isShared_1038_ = v_isSharedCheck_1043_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1044_ = leanh::lean_ctor_get(v___x_1034_, 0);
                        v_isSharedCheck_1051_ =
                            (!leanh::lean_is_exclusive(v___x_1034_)) as u8;
                        if v_isSharedCheck_1051_ == 0 {
                            v___x_1046_ = v___x_1034_;
                            v_isShared_1047_ = v_isSharedCheck_1051_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1044_);
                            leanh::lean_dec(v___x_1034_);
                            v___x_1046_ = leanh::lean_box(0);
                            v_isShared_1047_ = v_isSharedCheck_1051_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___f_1020_);
                    v___x_1052_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1052_, 0, v_acc_1022_);
                    return v___x_1052_;
                }
            }
            2 => {
                v_fst_1039_ = leanh::lean_ctor_get(v_a_1035_, 0);
                leanh::lean_inc(v_fst_1039_);
                leanh::lean_dec(v_a_1035_);
                if v_isShared_1038_ == 0 {
                    leanh::lean_ctor_set(v___x_1037_, 0, v_fst_1039_);
                    v___x_1041_ = v___x_1037_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1042_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_fst_1039_);
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
                    v_reuseFailAlloc_1050_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
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
    mut v___f_1057_: *mut leanh::LeanObject,
    mut v_env_1058_: *mut leanh::LeanObject,
    mut v_acc_1059_: *mut leanh::LeanObject,
    mut v_m_1060_: *mut leanh::LeanObject,
    mut v_ci_1061_: *mut leanh::LeanObject,
    mut v___y_1062_: *mut leanh::LeanObject,
    mut v___y_1063_: *mut leanh::LeanObject,
    mut v___y_1064_: *mut leanh::LeanObject,
    mut v___y_1065_: *mut leanh::LeanObject,
    mut v___y_1066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1065_);
    leanh::lean_dec_ref(v___y_1064_);
    leanh::lean_dec(v___y_1063_);
    leanh::lean_dec_ref(v___y_1062_);
    leanh::lean_dec_ref(v_ci_1061_);
    return v_res_1067_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___redArg(
    mut v_f_1068_: *mut leanh::LeanObject,
    mut v_keys_1069_: *mut leanh::LeanObject,
    mut v_vals_1070_: *mut leanh::LeanObject,
    mut v_i_1071_: *mut leanh::LeanObject,
    mut v_acc_1072_: *mut leanh::LeanObject,
    mut v___y_1073_: *mut leanh::LeanObject,
    mut v___y_1074_: *mut leanh::LeanObject,
    mut v___y_1075_: *mut leanh::LeanObject,
    mut v___y_1076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: u8 = 0;
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1078_ = lean_array_get_size(v_keys_1069_);
                v___x_1079_ = lean_nat_dec_lt(v_i_1071_, v___x_1078_);
                if v___x_1079_ == 0 {
                    leanh::lean_dec(v_i_1071_);
                    leanh::lean_dec_ref(v_f_1068_);
                    v___x_1080_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1080_, 0, v_acc_1072_);
                    return v___x_1080_;
                } else {
                    v_k_1081_ = lean_array_fget_borrowed(v_keys_1069_, v_i_1071_);
                    v_v_1082_ = lean_array_fget_borrowed(v_vals_1070_, v_i_1071_);
                    leanh::lean_inc_ref(v_f_1068_);
                    leanh::lean_inc(v___y_1076_);
                    leanh::lean_inc_ref(v___y_1075_);
                    leanh::lean_inc(v___y_1074_);
                    leanh::lean_inc_ref(v___y_1073_);
                    leanh::lean_inc(v_v_1082_);
                    leanh::lean_inc(v_k_1081_);
                    v___x_1083_ = leanh::lean_apply_8(
                        v_f_1068_,
                        v_acc_1072_,
                        v_k_1081_,
                        v_v_1082_,
                        v___y_1073_,
                        v___y_1074_,
                        v___y_1075_,
                        v___y_1076_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1083_) == 0 {
                        v_a_1084_ = leanh::lean_ctor_get(v___x_1083_, 0);
                        leanh::lean_inc(v_a_1084_);
                        leanh::lean_dec_ref_known(v___x_1083_, 1);
                        v___x_1085_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1086_ = lean_nat_add(v_i_1071_, v___x_1085_);
                        leanh::lean_dec(v_i_1071_);
                        v_i_1071_ = v___x_1086_;
                        v_acc_1072_ = v_a_1084_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_1071_);
                        leanh::lean_dec_ref(v_f_1068_);
                        return v___x_1083_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_f_1088_: *mut leanh::LeanObject,
    mut v_keys_1089_: *mut leanh::LeanObject,
    mut v_vals_1090_: *mut leanh::LeanObject,
    mut v_i_1091_: *mut leanh::LeanObject,
    mut v_acc_1092_: *mut leanh::LeanObject,
    mut v___y_1093_: *mut leanh::LeanObject,
    mut v___y_1094_: *mut leanh::LeanObject,
    mut v___y_1095_: *mut leanh::LeanObject,
    mut v___y_1096_: *mut leanh::LeanObject,
    mut v___y_1097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1098_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___redArg(v_f_1088_, v_keys_1089_, v_vals_1090_, v_i_1091_, v_acc_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
    leanh::lean_dec(v___y_1096_);
    leanh::lean_dec_ref(v___y_1095_);
    leanh::lean_dec(v___y_1094_);
    leanh::lean_dec_ref(v___y_1093_);
    leanh::lean_dec_ref(v_vals_1090_);
    leanh::lean_dec_ref(v_keys_1089_);
    return v_res_1098_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(
    mut v_f_1099_: *mut leanh::LeanObject,
    mut v_x_1100_: *mut leanh::LeanObject,
    mut v_x_1101_: *mut leanh::LeanObject,
    mut v___y_1102_: *mut leanh::LeanObject,
    mut v___y_1103_: *mut leanh::LeanObject,
    mut v___y_1104_: *mut leanh::LeanObject,
    mut v___y_1105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1110_: u8 = 0;
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: u8 = 0;
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: u8 = 0;
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: usize = 0;
    let mut v___x_1122_: usize = 0;
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: usize = 0;
    let mut v___x_1125_: usize = 0;
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1127_: u8 = 0;
    let mut v_ks_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1100_) == 0 {
                    v_es_1107_ = leanh::lean_ctor_get(v_x_1100_, 0);
                    v_isSharedCheck_1127_ = (!leanh::lean_is_exclusive(v_x_1100_)) as u8;
                    if v_isSharedCheck_1127_ == 0 {
                        v___x_1109_ = v_x_1100_;
                        v_isShared_1110_ = v_isSharedCheck_1127_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_es_1107_);
                        leanh::lean_dec(v_x_1100_);
                        v___x_1109_ = leanh::lean_box(0);
                        v_isShared_1110_ = v_isSharedCheck_1127_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_1128_ = leanh::lean_ctor_get(v_x_1100_, 0);
                    leanh::lean_inc_ref(v_ks_1128_);
                    v_vs_1129_ = leanh::lean_ctor_get(v_x_1100_, 1);
                    leanh::lean_inc_ref(v_vs_1129_);
                    leanh::lean_dec_ref_known(v_x_1100_, 2);
                    v___x_1130_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1131_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___redArg(v_f_1099_, v_ks_1128_, v_vs_1129_, v___x_1130_, v_x_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
                    leanh::lean_dec_ref(v_vs_1129_);
                    leanh::lean_dec_ref(v_ks_1128_);
                    return v___x_1131_;
                }
            }
            1 => {
                v___x_1111_ = leanh::lean_unsigned_to_nat(0);
                v___x_1112_ = lean_array_get_size(v_es_1107_);
                v___x_1113_ = lean_nat_dec_lt(v___x_1111_, v___x_1112_);
                if v___x_1113_ == 0 {
                    leanh::lean_dec_ref(v_es_1107_);
                    leanh::lean_dec_ref(v_f_1099_);
                    if v_isShared_1110_ == 0 {
                        leanh::lean_ctor_set(v___x_1109_, 0, v_x_1101_);
                        v___x_1115_ = v___x_1109_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1116_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_x_1101_);
                        v___x_1115_ = v_reuseFailAlloc_1116_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1117_ = lean_nat_dec_le(v___x_1112_, v___x_1112_);
                    if v___x_1117_ == 0 {
                        if v___x_1113_ == 0 {
                            leanh::lean_dec_ref(v_es_1107_);
                            leanh::lean_dec_ref(v_f_1099_);
                            if v_isShared_1110_ == 0 {
                                leanh::lean_ctor_set(v___x_1109_, 0, v_x_1101_);
                                v___x_1119_ = v___x_1109_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1120_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_x_1101_);
                                v___x_1119_ = v_reuseFailAlloc_1120_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1109_);
                            v___x_1121_ = 0usize;
                            v___x_1122_ = lean_usize_of_nat(v___x_1112_);
                            v___x_1123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(v_f_1099_, v_es_1107_, v___x_1121_, v___x_1122_, v_x_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
                            leanh::lean_dec_ref(v_es_1107_);
                            return v___x_1123_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1109_);
                        v___x_1124_ = 0usize;
                        v___x_1125_ = lean_usize_of_nat(v___x_1112_);
                        v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(v_f_1099_, v_es_1107_, v___x_1124_, v___x_1125_, v_x_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
                        leanh::lean_dec_ref(v_es_1107_);
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
    mut v_f_1132_: *mut leanh::LeanObject,
    mut v_as_1133_: *mut leanh::LeanObject,
    mut v_i_1134_: usize,
    mut v_stop_1135_: usize,
    mut v_b_1136_: *mut leanh::LeanObject,
    mut v___y_1137_: *mut leanh::LeanObject,
    mut v___y_1138_: *mut leanh::LeanObject,
    mut v___y_1139_: *mut leanh::LeanObject,
    mut v___y_1140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: usize = 0;
    let mut v___x_1145_: usize = 0;
    let mut v___y_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: u8 = 0;
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1150_ = lean_usize_dec_eq(v_i_1134_, v_stop_1135_);
                if v___x_1150_ == 0 {
                    v___x_1151_ = lean_array_uget_borrowed(v_as_1133_, v_i_1134_);
                    match leanh::lean_obj_tag(v___x_1151_) {
                        0 => {
                            v_key_1152_ = leanh::lean_ctor_get(v___x_1151_, 0);
                            v_val_1153_ = leanh::lean_ctor_get(v___x_1151_, 1);
                            leanh::lean_inc_ref(v_f_1132_);
                            leanh::lean_inc(v___y_1140_);
                            leanh::lean_inc_ref(v___y_1139_);
                            leanh::lean_inc(v___y_1138_);
                            leanh::lean_inc_ref(v___y_1137_);
                            leanh::lean_inc(v_val_1153_);
                            leanh::lean_inc(v_key_1152_);
                            v___x_1154_ = leanh::lean_apply_8(
                                v_f_1132_,
                                v_b_1136_,
                                v_key_1152_,
                                v_val_1153_,
                                v___y_1137_,
                                v___y_1138_,
                                v___y_1139_,
                                v___y_1140_,
                                leanh::lean_box(0),
                            );
                            v___y_1148_ = v___x_1154_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_1155_ = leanh::lean_ctor_get(v___x_1151_, 0);
                            leanh::lean_inc(v_node_1155_);
                            leanh::lean_inc_ref(v_f_1132_);
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
                    leanh::lean_dec_ref(v_f_1132_);
                    v___x_1157_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1157_, 0, v_b_1136_);
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
                if leanh::lean_obj_tag(v___y_1148_) == 0 {
                    v_a_1149_ = leanh::lean_ctor_get(v___y_1148_, 0);
                    leanh::lean_inc(v_a_1149_);
                    leanh::lean_dec_ref_known(v___y_1148_, 1);
                    v_a_1143_ = v_a_1149_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_f_1132_);
                    return v___y_1148_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_f_1158_: *mut leanh::LeanObject,
    mut v_as_1159_: *mut leanh::LeanObject,
    mut v_i_1160_: *mut leanh::LeanObject,
    mut v_stop_1161_: *mut leanh::LeanObject,
    mut v_b_1162_: *mut leanh::LeanObject,
    mut v___y_1163_: *mut leanh::LeanObject,
    mut v___y_1164_: *mut leanh::LeanObject,
    mut v___y_1165_: *mut leanh::LeanObject,
    mut v___y_1166_: *mut leanh::LeanObject,
    mut v___y_1167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1168_: usize = 0;
    let mut v_stop_boxed_1169_: usize = 0;
    let mut v_res_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1168_ = leanh::lean_unbox_usize(v_i_1160_);
    leanh::lean_dec(v_i_1160_);
    v_stop_boxed_1169_ = leanh::lean_unbox_usize(v_stop_1161_);
    leanh::lean_dec(v_stop_1161_);
    v_res_1170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(v_f_1158_, v_as_1159_, v_i_boxed_1168_, v_stop_boxed_1169_, v_b_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
    leanh::lean_dec(v___y_1166_);
    leanh::lean_dec_ref(v___y_1165_);
    leanh::lean_dec(v___y_1164_);
    leanh::lean_dec_ref(v___y_1163_);
    leanh::lean_dec_ref(v_as_1159_);
    return v_res_1170_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg___boxed(
    mut v_f_1171_: *mut leanh::LeanObject,
    mut v_x_1172_: *mut leanh::LeanObject,
    mut v_x_1173_: *mut leanh::LeanObject,
    mut v___y_1174_: *mut leanh::LeanObject,
    mut v___y_1175_: *mut leanh::LeanObject,
    mut v___y_1176_: *mut leanh::LeanObject,
    mut v___y_1177_: *mut leanh::LeanObject,
    mut v___y_1178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1179_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_1171_, v_x_1172_, v_x_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
    leanh::lean_dec(v___y_1177_);
    leanh::lean_dec_ref(v___y_1176_);
    leanh::lean_dec(v___y_1175_);
    leanh::lean_dec_ref(v___y_1174_);
    return v_res_1179_;
}
pub unsafe fn l_Lean_LibrarySuggestions_localSymbolFrequencyMap(
    mut v_a_1181_: *mut leanh::LeanObject,
    mut v_a_1182_: *mut leanh::LeanObject,
    mut v_a_1183_: *mut leanh::LeanObject,
    mut v_a_1184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1186_ = lean_st_ref_get(v_a_1184_);
    v_env_1187_ = leanh::lean_ctor_get(v___x_1186_, 0);
    leanh::lean_inc_ref_n(v_env_1187_, 2);
    leanh::lean_dec(v___x_1186_);
    v___x_1188_ = l_Lean_Environment_constants(v_env_1187_);
    v_map_u2082_1189_ = leanh::lean_ctor_get(v___x_1188_, 1);
    leanh::lean_inc_ref(v_map_u2082_1189_);
    leanh::lean_dec_ref(v___x_1188_);
    v___f_1190_ = l_Lean_LibrarySuggestions_localSymbolFrequencyMap___closed__0;
    v___f_1191_ = leanh::lean_alloc_closure(
        l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___boxed
            as *mut core::ffi::c_void,
        10,
        2,
    );
    leanh::lean_closure_set(v___f_1191_, 0, v___f_1190_);
    leanh::lean_closure_set(v___f_1191_, 1, v_env_1187_);
    v___x_1192_ = leanh::lean_box(1);
    v___x_1193_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v___f_1191_, v_map_u2082_1189_, v___x_1192_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
    return v___x_1193_;
}
pub unsafe fn l_Lean_LibrarySuggestions_localSymbolFrequencyMap___boxed(
    mut v_a_1194_: *mut leanh::LeanObject,
    mut v_a_1195_: *mut leanh::LeanObject,
    mut v_a_1196_: *mut leanh::LeanObject,
    mut v_a_1197_: *mut leanh::LeanObject,
    mut v_a_1198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1199_ = l_Lean_LibrarySuggestions_localSymbolFrequencyMap(
        v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_,
    );
    leanh::lean_dec(v_a_1197_);
    leanh::lean_dec_ref(v_a_1196_);
    leanh::lean_dec(v_a_1195_);
    leanh::lean_dec_ref(v_a_1194_);
    return v_res_1199_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0(
    mut v_k_1200_: *mut leanh::LeanObject,
    mut v_t_1201_: *mut leanh::LeanObject,
    mut v_hl_1202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1203_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__0___redArg(v_k_1200_, v_t_1201_);
    return v___x_1203_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1___redArg(
    mut v_map_1204_: *mut leanh::LeanObject,
    mut v_f_1205_: *mut leanh::LeanObject,
    mut v_init_1206_: *mut leanh::LeanObject,
    mut v___y_1207_: *mut leanh::LeanObject,
    mut v___y_1208_: *mut leanh::LeanObject,
    mut v___y_1209_: *mut leanh::LeanObject,
    mut v___y_1210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1212_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_1205_, v_map_1204_, v_init_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
    return v___x_1212_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1___redArg___boxed(
    mut v_map_1213_: *mut leanh::LeanObject,
    mut v_f_1214_: *mut leanh::LeanObject,
    mut v_init_1215_: *mut leanh::LeanObject,
    mut v___y_1216_: *mut leanh::LeanObject,
    mut v___y_1217_: *mut leanh::LeanObject,
    mut v___y_1218_: *mut leanh::LeanObject,
    mut v___y_1219_: *mut leanh::LeanObject,
    mut v___y_1220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1221_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1___redArg(v_map_1213_, v_f_1214_, v_init_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
    leanh::lean_dec(v___y_1219_);
    leanh::lean_dec_ref(v___y_1218_);
    leanh::lean_dec(v___y_1217_);
    leanh::lean_dec_ref(v___y_1216_);
    return v_res_1221_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1(
    mut v_00_u03c3_1222_: *mut leanh::LeanObject,
    mut v_00_u03b2_1223_: *mut leanh::LeanObject,
    mut v_map_1224_: *mut leanh::LeanObject,
    mut v_f_1225_: *mut leanh::LeanObject,
    mut v_init_1226_: *mut leanh::LeanObject,
    mut v___y_1227_: *mut leanh::LeanObject,
    mut v___y_1228_: *mut leanh::LeanObject,
    mut v___y_1229_: *mut leanh::LeanObject,
    mut v___y_1230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1232_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_1225_, v_map_1224_, v_init_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
    return v___x_1232_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1___boxed(
    mut v_00_u03c3_1233_: *mut leanh::LeanObject,
    mut v_00_u03b2_1234_: *mut leanh::LeanObject,
    mut v_map_1235_: *mut leanh::LeanObject,
    mut v_f_1236_: *mut leanh::LeanObject,
    mut v_init_1237_: *mut leanh::LeanObject,
    mut v___y_1238_: *mut leanh::LeanObject,
    mut v___y_1239_: *mut leanh::LeanObject,
    mut v___y_1240_: *mut leanh::LeanObject,
    mut v___y_1241_: *mut leanh::LeanObject,
    mut v___y_1242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1243_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1(v_00_u03c3_1233_, v_00_u03b2_1234_, v_map_1235_, v_f_1236_, v_init_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
    leanh::lean_dec(v___y_1241_);
    leanh::lean_dec_ref(v___y_1240_);
    leanh::lean_dec(v___y_1239_);
    leanh::lean_dec_ref(v___y_1238_);
    return v_res_1243_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1(
    mut v_00_u03c3_1244_: *mut leanh::LeanObject,
    mut v_00_u03b1_1245_: *mut leanh::LeanObject,
    mut v_00_u03b2_1246_: *mut leanh::LeanObject,
    mut v_f_1247_: *mut leanh::LeanObject,
    mut v_x_1248_: *mut leanh::LeanObject,
    mut v_x_1249_: *mut leanh::LeanObject,
    mut v___y_1250_: *mut leanh::LeanObject,
    mut v___y_1251_: *mut leanh::LeanObject,
    mut v___y_1252_: *mut leanh::LeanObject,
    mut v___y_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1255_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___redArg(v_f_1247_, v_x_1248_, v_x_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
    return v___x_1255_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1___boxed(
    mut v_00_u03c3_1256_: *mut leanh::LeanObject,
    mut v_00_u03b1_1257_: *mut leanh::LeanObject,
    mut v_00_u03b2_1258_: *mut leanh::LeanObject,
    mut v_f_1259_: *mut leanh::LeanObject,
    mut v_x_1260_: *mut leanh::LeanObject,
    mut v_x_1261_: *mut leanh::LeanObject,
    mut v___y_1262_: *mut leanh::LeanObject,
    mut v___y_1263_: *mut leanh::LeanObject,
    mut v___y_1264_: *mut leanh::LeanObject,
    mut v___y_1265_: *mut leanh::LeanObject,
    mut v___y_1266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1267_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1(v_00_u03c3_1256_, v_00_u03b1_1257_, v_00_u03b2_1258_, v_f_1259_, v_x_1260_, v_x_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
    leanh::lean_dec(v___y_1265_);
    leanh::lean_dec_ref(v___y_1264_);
    leanh::lean_dec(v___y_1263_);
    leanh::lean_dec_ref(v___y_1262_);
    return v_res_1267_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2(
    mut v_00_u03b1_1268_: *mut leanh::LeanObject,
    mut v_00_u03b2_1269_: *mut leanh::LeanObject,
    mut v_00_u03c3_1270_: *mut leanh::LeanObject,
    mut v_f_1271_: *mut leanh::LeanObject,
    mut v_as_1272_: *mut leanh::LeanObject,
    mut v_i_1273_: usize,
    mut v_stop_1274_: usize,
    mut v_b_1275_: *mut leanh::LeanObject,
    mut v___y_1276_: *mut leanh::LeanObject,
    mut v___y_1277_: *mut leanh::LeanObject,
    mut v___y_1278_: *mut leanh::LeanObject,
    mut v___y_1279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___redArg(v_f_1271_, v_as_1272_, v_i_1273_, v_stop_1274_, v_b_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
    return v___x_1281_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b1_1282_: *mut leanh::LeanObject,
    mut v_00_u03b2_1283_: *mut leanh::LeanObject,
    mut v_00_u03c3_1284_: *mut leanh::LeanObject,
    mut v_f_1285_: *mut leanh::LeanObject,
    mut v_as_1286_: *mut leanh::LeanObject,
    mut v_i_1287_: *mut leanh::LeanObject,
    mut v_stop_1288_: *mut leanh::LeanObject,
    mut v_b_1289_: *mut leanh::LeanObject,
    mut v___y_1290_: *mut leanh::LeanObject,
    mut v___y_1291_: *mut leanh::LeanObject,
    mut v___y_1292_: *mut leanh::LeanObject,
    mut v___y_1293_: *mut leanh::LeanObject,
    mut v___y_1294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1295_: usize = 0;
    let mut v_stop_boxed_1296_: usize = 0;
    let mut v_res_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1295_ = leanh::lean_unbox_usize(v_i_1287_);
    leanh::lean_dec(v_i_1287_);
    v_stop_boxed_1296_ = leanh::lean_unbox_usize(v_stop_1288_);
    leanh::lean_dec(v_stop_1288_);
    v_res_1297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__2(v_00_u03b1_1282_, v_00_u03b2_1283_, v_00_u03c3_1284_, v_f_1285_, v_as_1286_, v_i_boxed_1295_, v_stop_boxed_1296_, v_b_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
    leanh::lean_dec(v___y_1293_);
    leanh::lean_dec_ref(v___y_1292_);
    leanh::lean_dec(v___y_1291_);
    leanh::lean_dec_ref(v___y_1290_);
    leanh::lean_dec_ref(v_as_1286_);
    return v_res_1297_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3(
    mut v_00_u03c3_1298_: *mut leanh::LeanObject,
    mut v_00_u03b1_1299_: *mut leanh::LeanObject,
    mut v_00_u03b2_1300_: *mut leanh::LeanObject,
    mut v_f_1301_: *mut leanh::LeanObject,
    mut v_keys_1302_: *mut leanh::LeanObject,
    mut v_vals_1303_: *mut leanh::LeanObject,
    mut v_heq_1304_: *mut leanh::LeanObject,
    mut v_i_1305_: *mut leanh::LeanObject,
    mut v_acc_1306_: *mut leanh::LeanObject,
    mut v___y_1307_: *mut leanh::LeanObject,
    mut v___y_1308_: *mut leanh::LeanObject,
    mut v___y_1309_: *mut leanh::LeanObject,
    mut v___y_1310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1312_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___redArg(v_f_1301_, v_keys_1302_, v_vals_1303_, v_i_1305_, v_acc_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
    return v___x_1312_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3___boxed(
    mut v_00_u03c3_1313_: *mut leanh::LeanObject,
    mut v_00_u03b1_1314_: *mut leanh::LeanObject,
    mut v_00_u03b2_1315_: *mut leanh::LeanObject,
    mut v_f_1316_: *mut leanh::LeanObject,
    mut v_keys_1317_: *mut leanh::LeanObject,
    mut v_vals_1318_: *mut leanh::LeanObject,
    mut v_heq_1319_: *mut leanh::LeanObject,
    mut v_i_1320_: *mut leanh::LeanObject,
    mut v_acc_1321_: *mut leanh::LeanObject,
    mut v___y_1322_: *mut leanh::LeanObject,
    mut v___y_1323_: *mut leanh::LeanObject,
    mut v___y_1324_: *mut leanh::LeanObject,
    mut v___y_1325_: *mut leanh::LeanObject,
    mut v___y_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1327_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_LibrarySuggestions_localSymbolFrequencyMap_spec__1_spec__1_spec__3(v_00_u03c3_1313_, v_00_u03b1_1314_, v_00_u03b2_1315_, v_f_1316_, v_keys_1317_, v_vals_1318_, v_heq_1319_, v_i_1320_, v_acc_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
    leanh::lean_dec(v___y_1325_);
    leanh::lean_dec_ref(v___y_1324_);
    leanh::lean_dec(v___y_1323_);
    leanh::lean_dec_ref(v___y_1322_);
    leanh::lean_dec_ref(v_vals_1318_);
    leanh::lean_dec_ref(v_keys_1317_);
    return v_res_1327_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1329_ = leanh::lean_box(0);
    v___x_1330_ = lean_st_mk_ref(v___x_1329_);
    v___x_1331_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1331_, 0, v___x_1330_);
    return v___x_1331_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2____boxed(
    mut v_a_1332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1333_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2_();
    return v_res_1333_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap(
    mut v_a_1334_: *mut leanh::LeanObject,
    mut v_a_1335_: *mut leanh::LeanObject,
    mut v_a_1336_: *mut leanh::LeanObject,
    mut v_a_1337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1345_: u8 = 0;
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1351_: u8 = 0;
    let mut v_val_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1355_: u8 = 0;
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1359_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1339_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_localSymbolFrequencyMapRef;
                v___x_1340_ = lean_st_ref_get(v___x_1339_);
                if leanh::lean_obj_tag(v___x_1340_) == 0 {
                    v___x_1341_ = l_Lean_LibrarySuggestions_localSymbolFrequencyMap(
                        v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_,
                    );
                    if leanh::lean_obj_tag(v___x_1341_) == 0 {
                        v_a_1342_ = leanh::lean_ctor_get(v___x_1341_, 0);
                        v_isSharedCheck_1351_ =
                            (!leanh::lean_is_exclusive(v___x_1341_)) as u8;
                        if v_isSharedCheck_1351_ == 0 {
                            v___x_1344_ = v___x_1341_;
                            v_isShared_1345_ = v_isSharedCheck_1351_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1342_);
                            leanh::lean_dec(v___x_1341_);
                            v___x_1344_ = leanh::lean_box(0);
                            v_isShared_1345_ = v_isSharedCheck_1351_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_1341_;
                    }
                } else {
                    v_val_1352_ = leanh::lean_ctor_get(v___x_1340_, 0);
                    v_isSharedCheck_1359_ = (!leanh::lean_is_exclusive(v___x_1340_)) as u8;
                    if v_isSharedCheck_1359_ == 0 {
                        v___x_1354_ = v___x_1340_;
                        v_isShared_1355_ = v_isSharedCheck_1359_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1352_);
                        leanh::lean_dec(v___x_1340_);
                        v___x_1354_ = leanh::lean_box(0);
                        v_isShared_1355_ = v_isSharedCheck_1359_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_1342_);
                v___x_1346_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1346_, 0, v_a_1342_);
                v___x_1347_ = lean_st_ref_set(v___x_1339_, v___x_1346_);
                if v_isShared_1345_ == 0 {
                    v___x_1349_ = v___x_1344_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1350_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1342_);
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
                    leanh::lean_ctor_set_tag(v___x_1354_, 0);
                    v___x_1357_ = v___x_1354_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1358_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_val_1352_);
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
    mut v_a_1360_: *mut leanh::LeanObject,
    mut v_a_1361_: *mut leanh::LeanObject,
    mut v_a_1362_: *mut leanh::LeanObject,
    mut v_a_1363_: *mut leanh::LeanObject,
    mut v_a_1364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1365_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap(v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
    leanh::lean_dec(v_a_1363_);
    leanh::lean_dec_ref(v_a_1362_);
    leanh::lean_dec(v_a_1361_);
    leanh::lean_dec_ref(v_a_1360_);
    return v_res_1365_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(
    mut v_t_1366_: *mut leanh::LeanObject,
    mut v_k_1367_: *mut leanh::LeanObject,
    mut v_fallback_1368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1366_) == 0 {
                    v_k_1369_ = leanh::lean_ctor_get(v_t_1366_, 1);
                    v_v_1370_ = leanh::lean_ctor_get(v_t_1366_, 2);
                    v_l_1371_ = leanh::lean_ctor_get(v_t_1366_, 3);
                    v_r_1372_ = leanh::lean_ctor_get(v_t_1366_, 4);
                    v___x_1373_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1367_, v_k_1369_);
                    match v___x_1373_ {
                        0 => {
                            v_t_1366_ = v_l_1371_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            leanh::lean_inc(v_v_1370_);
                            return v_v_1370_;
                        }
                        _ => {
                            v_t_1366_ = v_r_1372_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_fallback_1368_);
                    return v_fallback_1368_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg___boxed(
    mut v_t_1376_: *mut leanh::LeanObject,
    mut v_k_1377_: *mut leanh::LeanObject,
    mut v_fallback_1378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1379_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_t_1376_, v_k_1377_, v_fallback_1378_);
    leanh::lean_dec(v_fallback_1378_);
    leanh::lean_dec(v_k_1377_);
    leanh::lean_dec(v_t_1376_);
    return v_res_1379_;
}
pub unsafe fn l_Lean_LibrarySuggestions_localSymbolFrequency(
    mut v_n_1380_: *mut leanh::LeanObject,
    mut v_a_1381_: *mut leanh::LeanObject,
    mut v_a_1382_: *mut leanh::LeanObject,
    mut v_a_1383_: *mut leanh::LeanObject,
    mut v_a_1384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1390_: u8 = 0;
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1396_: u8 = 0;
    let mut v_a_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1400_: u8 = 0;
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1404_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1386_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap(v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
                if leanh::lean_obj_tag(v___x_1386_) == 0 {
                    v_a_1387_ = leanh::lean_ctor_get(v___x_1386_, 0);
                    v_isSharedCheck_1396_ = (!leanh::lean_is_exclusive(v___x_1386_)) as u8;
                    if v_isSharedCheck_1396_ == 0 {
                        v___x_1389_ = v___x_1386_;
                        v_isShared_1390_ = v_isSharedCheck_1396_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1387_);
                        leanh::lean_dec(v___x_1386_);
                        v___x_1389_ = leanh::lean_box(0);
                        v_isShared_1390_ = v_isSharedCheck_1396_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1397_ = leanh::lean_ctor_get(v___x_1386_, 0);
                    v_isSharedCheck_1404_ = (!leanh::lean_is_exclusive(v___x_1386_)) as u8;
                    if v_isSharedCheck_1404_ == 0 {
                        v___x_1399_ = v___x_1386_;
                        v_isShared_1400_ = v_isSharedCheck_1404_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1397_);
                        leanh::lean_dec(v___x_1386_);
                        v___x_1399_ = leanh::lean_box(0);
                        v_isShared_1400_ = v_isSharedCheck_1404_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1391_ = leanh::lean_unsigned_to_nat(0);
                v___x_1392_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_a_1387_, v_n_1380_, v___x_1391_);
                leanh::lean_dec(v_a_1387_);
                if v_isShared_1390_ == 0 {
                    leanh::lean_ctor_set(v___x_1389_, 0, v___x_1392_);
                    v___x_1394_ = v___x_1389_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1395_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
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
                    v_reuseFailAlloc_1403_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
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
    mut v_n_1405_: *mut leanh::LeanObject,
    mut v_a_1406_: *mut leanh::LeanObject,
    mut v_a_1407_: *mut leanh::LeanObject,
    mut v_a_1408_: *mut leanh::LeanObject,
    mut v_a_1409_: *mut leanh::LeanObject,
    mut v_a_1410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1411_ = l_Lean_LibrarySuggestions_localSymbolFrequency(
        v_n_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_,
    );
    leanh::lean_dec(v_a_1409_);
    leanh::lean_dec_ref(v_a_1408_);
    leanh::lean_dec(v_a_1407_);
    leanh::lean_dec_ref(v_a_1406_);
    leanh::lean_dec(v_n_1405_);
    return v_res_1411_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0(
    mut v_00_u03b4_1412_: *mut leanh::LeanObject,
    mut v_t_1413_: *mut leanh::LeanObject,
    mut v_k_1414_: *mut leanh::LeanObject,
    mut v_fallback_1415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1416_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_t_1413_, v_k_1414_, v_fallback_1415_);
    return v___x_1416_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___boxed(
    mut v_00_u03b4_1417_: *mut leanh::LeanObject,
    mut v_t_1418_: *mut leanh::LeanObject,
    mut v_k_1419_: *mut leanh::LeanObject,
    mut v_fallback_1420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1421_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0(v_00_u03b4_1417_, v_t_1418_, v_k_1419_, v_fallback_1420_);
    leanh::lean_dec(v_fallback_1420_);
    leanh::lean_dec(v_k_1419_);
    leanh::lean_dec(v_t_1418_);
    return v_res_1421_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___lam__0(
    mut v___x_1422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1424_ = l_Lean_MessageData_toString(v___x_1422_);
    v___x_1425_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1425_, 0, v___x_1424_);
    return v___x_1425_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___lam__0___boxed(
    mut v___x_1426_: *mut leanh::LeanObject,
    mut v___y_1427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1428_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___lam__0(v___x_1426_);
    return v_res_1428_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1429_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_1429_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1430_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__0);
    v___x_1431_ = l_StateRefT_x27_instMonad___redArg(v___x_1430_);
    return v___x_1431_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12()
-> u64 {
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: u64 = 0;
    v___x_1451_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11;
    v___x_1452_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1451_);
    return v___x_1452_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1453_: u64 = 0;
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1453_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__12);
    v___x_1454_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__11;
    v___x_1455_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
    leanh::lean_ctor_set(v___x_1455_, 0, v___x_1454_);
    leanh::lean_ctor_set_uint64(
        v___x_1455_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1453_,
    );
    return v___x_1455_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1456_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1456_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1457_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__14);
    v___x_1458_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1458_, 0, v___x_1457_);
    return v___x_1458_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1459_ = leanh::lean_unsigned_to_nat(32);
    v___x_1460_ = lean_mk_empty_array_with_capacity(v___x_1459_);
    v___x_1461_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1461_, 0, v___x_1460_);
    return v___x_1461_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1462_: usize = 0;
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1462_ = 5usize;
    v___x_1463_ = leanh::lean_unsigned_to_nat(0);
    v___x_1464_ = leanh::lean_unsigned_to_nat(32);
    v___x_1465_ = lean_mk_empty_array_with_capacity(v___x_1464_);
    v___x_1466_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__16);
    v___x_1467_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1467_, 0, v___x_1466_);
    leanh::lean_ctor_set(v___x_1467_, 1, v___x_1465_);
    leanh::lean_ctor_set(v___x_1467_, 2, v___x_1463_);
    leanh::lean_ctor_set(v___x_1467_, 3, v___x_1463_);
    leanh::lean_ctor_set_usize(v___x_1467_, 4, v___x_1462_);
    return v___x_1467_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1468_ = leanh::lean_box(1);
    v___x_1469_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
    v___x_1470_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
    v___x_1471_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1471_, 0, v___x_1470_);
    leanh::lean_ctor_set(v___x_1471_, 1, v___x_1469_);
    leanh::lean_ctor_set(v___x_1471_, 2, v___x_1468_);
    return v___x_1471_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_1474_: u8 = 0;
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: u8 = 0;
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1474_ = 1;
    v___x_1475_ = leanh::lean_unsigned_to_nat(0);
    v___x_1476_ = leanh::lean_box(0);
    v___x_1477_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__19;
    v___x_1478_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__18);
    v___x_1479_ = leanh::lean_box(1);
    v___x_1480_ = 0;
    v___x_1481_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__13);
    v___x_1482_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
    leanh::lean_ctor_set(v___x_1482_, 0, v___x_1481_);
    leanh::lean_ctor_set(v___x_1482_, 1, v___x_1479_);
    leanh::lean_ctor_set(v___x_1482_, 2, v___x_1478_);
    leanh::lean_ctor_set(v___x_1482_, 3, v___x_1477_);
    leanh::lean_ctor_set(v___x_1482_, 4, v___x_1476_);
    leanh::lean_ctor_set(v___x_1482_, 5, v___x_1475_);
    leanh::lean_ctor_set(v___x_1482_, 6, v___x_1476_);
    leanh::lean_ctor_set_uint8(
        v___x_1482_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
        v___x_1480_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1482_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
        v___x_1480_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1482_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
        v___x_1480_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1482_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
        v___x_1474_,
    );
    return v___x_1482_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1483_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
    v___x_1484_ = leanh::lean_unsigned_to_nat(0);
    v___x_1485_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1485_, 0, v___x_1484_);
    leanh::lean_ctor_set(v___x_1485_, 1, v___x_1484_);
    leanh::lean_ctor_set(v___x_1485_, 2, v___x_1484_);
    leanh::lean_ctor_set(v___x_1485_, 3, v___x_1484_);
    leanh::lean_ctor_set(v___x_1485_, 4, v___x_1483_);
    leanh::lean_ctor_set(v___x_1485_, 5, v___x_1483_);
    leanh::lean_ctor_set(v___x_1485_, 6, v___x_1483_);
    leanh::lean_ctor_set(v___x_1485_, 7, v___x_1483_);
    leanh::lean_ctor_set(v___x_1485_, 8, v___x_1483_);
    leanh::lean_ctor_set(v___x_1485_, 9, v___x_1483_);
    return v___x_1485_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1486_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
    v___x_1487_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_1487_, 0, v___x_1486_);
    leanh::lean_ctor_set(v___x_1487_, 1, v___x_1486_);
    leanh::lean_ctor_set(v___x_1487_, 2, v___x_1486_);
    leanh::lean_ctor_set(v___x_1487_, 3, v___x_1486_);
    leanh::lean_ctor_set(v___x_1487_, 4, v___x_1486_);
    leanh::lean_ctor_set(v___x_1487_, 5, v___x_1486_);
    return v___x_1487_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1488_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
    v___x_1489_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_1489_, 0, v___x_1488_);
    leanh::lean_ctor_set(v___x_1489_, 1, v___x_1488_);
    leanh::lean_ctor_set(v___x_1489_, 2, v___x_1488_);
    leanh::lean_ctor_set(v___x_1489_, 3, v___x_1488_);
    leanh::lean_ctor_set(v___x_1489_, 4, v___x_1488_);
    return v___x_1489_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1490_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__23);
    v___x_1491_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
    v___x_1492_ = leanh::lean_box(1);
    v___x_1493_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__22);
    v___x_1494_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__21);
    v___x_1495_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_1495_, 0, v___x_1494_);
    leanh::lean_ctor_set(v___x_1495_, 1, v___x_1493_);
    leanh::lean_ctor_set(v___x_1495_, 2, v___x_1492_);
    leanh::lean_ctor_set(v___x_1495_, 3, v___x_1491_);
    leanh::lean_ctor_set(v___x_1495_, 4, v___x_1490_);
    return v___x_1495_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: u8 = 0;
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2_once
        ),
        _init_l_Lean_LibrarySuggestions_localSymbolFrequencyMap___lam__1___closed__2,
    );
    v___x_1498_ = leanh::lean_box(0);
    v___x_1499_ = 0;
    v___x_1500_ = l_Lean_firstFrontendMacroScope;
    v___x_1501_ = leanh::lean_box(0);
    v___x_1502_ = leanh::lean_box(0);
    v___x_1503_ = leanh::lean_box(0);
    v___x_1504_ = leanh::lean_unsigned_to_nat(1000);
    v___x_1505_ = leanh::lean_unsigned_to_nat(0);
    v___x_1506_ = l_Lean_Options_empty;
    v___x_1507_ = l_Lean_instInhabitedFileMap_default;
    v___x_1508_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__25;
    v___x_1509_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_1509_, 0, v___x_1508_);
    leanh::lean_ctor_set(v___x_1509_, 1, v___x_1507_);
    leanh::lean_ctor_set(v___x_1509_, 2, v___x_1506_);
    leanh::lean_ctor_set(v___x_1509_, 3, v___x_1505_);
    leanh::lean_ctor_set(v___x_1509_, 4, v___x_1504_);
    leanh::lean_ctor_set(v___x_1509_, 5, v___x_1503_);
    leanh::lean_ctor_set(v___x_1509_, 6, v___x_1502_);
    leanh::lean_ctor_set(v___x_1509_, 7, v___x_1501_);
    leanh::lean_ctor_set(v___x_1509_, 8, v___x_1505_);
    leanh::lean_ctor_set(v___x_1509_, 9, v___x_1505_);
    leanh::lean_ctor_set(v___x_1509_, 10, v___x_1502_);
    leanh::lean_ctor_set(v___x_1509_, 11, v___x_1500_);
    leanh::lean_ctor_set(v___x_1509_, 12, v___x_1498_);
    leanh::lean_ctor_set(v___x_1509_, 13, v___x_1497_);
    leanh::lean_ctor_set_uint8(
        v___x_1509_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v___x_1499_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1509_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v___x_1499_,
    );
    return v___x_1509_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1510_ = leanh::lean_unsigned_to_nat(1);
    v___x_1511_ = l_Lean_firstFrontendMacroScope;
    v___x_1512_ = lean_nat_add(v___x_1511_, v___x_1510_);
    return v___x_1512_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32()
-> *mut leanh::LeanObject {
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: u64 = 0;
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1523_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
    v___x_1524_ = 0u64;
    v___x_1525_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
    leanh::lean_ctor_set(v___x_1525_, 0, v___x_1523_);
    leanh::lean_ctor_set_uint64(
        v___x_1525_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1524_,
    );
    return v___x_1525_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33()
-> *mut leanh::LeanObject {
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1526_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
    v___x_1527_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1527_, 0, v___x_1526_);
    leanh::lean_ctor_set(v___x_1527_, 1, v___x_1526_);
    return v___x_1527_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34()
-> *mut leanh::LeanObject {
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = l_Lean_NameSet_empty;
    v___x_1529_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
    v___x_1530_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1530_, 0, v___x_1529_);
    leanh::lean_ctor_set(v___x_1530_, 1, v___x_1529_);
    leanh::lean_ctor_set(v___x_1530_, 2, v___x_1528_);
    return v___x_1530_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35()
-> *mut leanh::LeanObject {
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: u8 = 0;
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__17);
    v___x_1532_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__15);
    v___x_1533_ = 1;
    v___x_1534_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_1534_, 0, v___x_1532_);
    leanh::lean_ctor_set(v___x_1534_, 1, v___x_1532_);
    leanh::lean_ctor_set(v___x_1534_, 2, v___x_1531_);
    leanh::lean_ctor_set_uint8(
        v___x_1534_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_1533_,
    );
    return v___x_1534_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(
    mut v_inst_1537_: *mut leanh::LeanObject,
    mut v_env_1538_: *mut leanh::LeanObject,
    mut v_x_1539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1560_: u8 = 0;
    let mut v_toFunctor_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1567_: u8 = 0;
    let mut v___f_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: u8 = 0;
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1619_: u8 = 0;
    let mut v_unused_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1621_: u8 = 0;
    let mut v_unused_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1540_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__1);
                v_toApplicative_1541_ = leanh::lean_ctor_get(v___x_1540_, 0);
                v_toFunctor_1542_ = leanh::lean_ctor_get(v_toApplicative_1541_, 0);
                v_toSeq_1543_ = leanh::lean_ctor_get(v_toApplicative_1541_, 2);
                v_toSeqLeft_1544_ = leanh::lean_ctor_get(v_toApplicative_1541_, 3);
                v_toSeqRight_1545_ = leanh::lean_ctor_get(v_toApplicative_1541_, 4);
                v___f_1546_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__2;
                v___f_1547_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_1542_, 2);
                v___f_1548_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1548_, 0, v_toFunctor_1542_);
                v___f_1549_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1549_, 0, v_toFunctor_1542_);
                v___x_1550_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1550_, 0, v___f_1548_);
                leanh::lean_ctor_set(v___x_1550_, 1, v___f_1549_);
                leanh::lean_inc(v_toSeqRight_1545_);
                v___f_1551_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1551_, 0, v_toSeqRight_1545_);
                leanh::lean_inc(v_toSeqLeft_1544_);
                v___f_1552_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1552_, 0, v_toSeqLeft_1544_);
                leanh::lean_inc(v_toSeq_1543_);
                v___f_1553_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1553_, 0, v_toSeq_1543_);
                v___x_1554_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_1554_, 0, v___x_1550_);
                leanh::lean_ctor_set(v___x_1554_, 1, v___f_1546_);
                leanh::lean_ctor_set(v___x_1554_, 2, v___f_1553_);
                leanh::lean_ctor_set(v___x_1554_, 3, v___f_1552_);
                leanh::lean_ctor_set(v___x_1554_, 4, v___f_1551_);
                v___x_1555_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1555_, 0, v___x_1554_);
                leanh::lean_ctor_set(v___x_1555_, 1, v___f_1547_);
                v___x_1556_ = l_StateRefT_x27_instMonad___redArg(v___x_1555_);
                v_toApplicative_1557_ = leanh::lean_ctor_get(v___x_1556_, 0);
                v_isSharedCheck_1621_ = (!leanh::lean_is_exclusive(v___x_1556_)) as u8;
                if v_isSharedCheck_1621_ == 0 {
                    v_unused_1622_ = leanh::lean_ctor_get(v___x_1556_, 1);
                    leanh::lean_dec(v_unused_1622_);
                    v___x_1559_ = v___x_1556_;
                    v_isShared_1560_ = v_isSharedCheck_1621_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_1557_);
                    leanh::lean_dec(v___x_1556_);
                    v___x_1559_ = leanh::lean_box(0);
                    v_isShared_1560_ = v_isSharedCheck_1621_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1561_ = leanh::lean_ctor_get(v_toApplicative_1557_, 0);
                v_toSeq_1562_ = leanh::lean_ctor_get(v_toApplicative_1557_, 2);
                v_toSeqLeft_1563_ = leanh::lean_ctor_get(v_toApplicative_1557_, 3);
                v_toSeqRight_1564_ = leanh::lean_ctor_get(v_toApplicative_1557_, 4);
                v_isSharedCheck_1619_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_1557_)) as u8;
                if v_isSharedCheck_1619_ == 0 {
                    v_unused_1620_ = leanh::lean_ctor_get(v_toApplicative_1557_, 1);
                    leanh::lean_dec(v_unused_1620_);
                    v___x_1566_ = v_toApplicative_1557_;
                    v_isShared_1567_ = v_isSharedCheck_1619_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_1564_);
                    leanh::lean_inc(v_toSeqLeft_1563_);
                    leanh::lean_inc(v_toSeq_1562_);
                    leanh::lean_inc(v_toFunctor_1561_);
                    leanh::lean_dec(v_toApplicative_1557_);
                    v___x_1566_ = leanh::lean_box(0);
                    v_isShared_1567_ = v_isSharedCheck_1619_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1568_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__4;
                v___f_1569_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__5;
                leanh::lean_inc_ref(v_toFunctor_1561_);
                v___f_1570_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1570_, 0, v_toFunctor_1561_);
                v___f_1571_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1571_, 0, v_toFunctor_1561_);
                v___x_1572_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1572_, 0, v___f_1570_);
                leanh::lean_ctor_set(v___x_1572_, 1, v___f_1571_);
                v___f_1573_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1573_, 0, v_toSeqRight_1564_);
                v___f_1574_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1574_, 0, v_toSeqLeft_1563_);
                v___f_1575_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1575_, 0, v_toSeq_1562_);
                if v_isShared_1567_ == 0 {
                    leanh::lean_ctor_set(v___x_1566_, 4, v___f_1573_);
                    leanh::lean_ctor_set(v___x_1566_, 3, v___f_1574_);
                    leanh::lean_ctor_set(v___x_1566_, 2, v___f_1575_);
                    leanh::lean_ctor_set(v___x_1566_, 1, v___f_1568_);
                    leanh::lean_ctor_set(v___x_1566_, 0, v___x_1572_);
                    v___x_1577_ = v___x_1566_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1618_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1572_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 1, v___f_1568_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 2, v___f_1575_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 3, v___f_1574_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 4, v___f_1573_);
                    v___x_1577_ = v_reuseFailAlloc_1618_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1560_ == 0 {
                    leanh::lean_ctor_set(v___x_1559_, 1, v___f_1569_);
                    leanh::lean_ctor_set(v___x_1559_, 0, v___x_1577_);
                    v___x_1579_ = v___x_1559_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1617_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1577_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1617_, 1, v___f_1569_);
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
                v___x_1585_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__20);
                v___x_1586_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__24);
                v___x_1587_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_MetaM_run_x27___boxed as *mut core::ffi::c_void,
                    7,
                    4,
                );
                leanh::lean_closure_set(v___x_1587_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_1587_, 1, v___x_1583_);
                leanh::lean_closure_set(v___x_1587_, 2, v___x_1585_);
                leanh::lean_closure_set(v___x_1587_, 3, v___x_1586_);
                v___x_1588_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__26);
                v___x_1589_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__27);
                v___x_1590_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__30;
                v___x_1591_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__31;
                v___x_1592_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__32);
                v___x_1593_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__33);
                v___x_1594_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__34);
                v___x_1595_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__35);
                v___x_1596_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                leanh::lean_ctor_set(v___x_1596_, 0, v_env_1538_);
                leanh::lean_ctor_set(v___x_1596_, 1, v___x_1589_);
                leanh::lean_ctor_set(v___x_1596_, 2, v___x_1590_);
                leanh::lean_ctor_set(v___x_1596_, 3, v___x_1591_);
                leanh::lean_ctor_set(v___x_1596_, 4, v___x_1592_);
                leanh::lean_ctor_set(v___x_1596_, 5, v___x_1593_);
                leanh::lean_ctor_set(v___x_1596_, 6, v___x_1594_);
                leanh::lean_ctor_set(v___x_1596_, 7, v___x_1595_);
                leanh::lean_ctor_set(v___x_1596_, 8, v___x_1584_);
                v___x_1597_ = leanh::lean_alloc_closure(
                    l_Lean_Core_CoreM_run_x27___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                leanh::lean_closure_set(v___x_1597_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_1597_, 1, v___x_1587_);
                leanh::lean_closure_set(v___x_1597_, 2, v___x_1588_);
                leanh::lean_closure_set(v___x_1597_, 3, v___x_1596_);
                v___x_1598_ = leanh::lean_alloc_closure(
                    l_EIO_toBaseIO___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___x_1598_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_1598_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_1598_, 2, v___x_1597_);
                v___x_1599_ = l_unsafeBaseIO___redArg(v___x_1598_);
                if leanh::lean_obj_tag(v___x_1599_) == 0 {
                    v_a_1600_ = leanh::lean_ctor_get(v___x_1599_, 0);
                    leanh::lean_inc(v_a_1600_);
                    leanh::lean_dec_ref_known(v___x_1599_, 1);
                    v___x_1601_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__36;
                    v___x_1602_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___closed__37;
                    v___x_1603_ = leanh::lean_unsigned_to_nat(75);
                    v___x_1604_ = leanh::lean_unsigned_to_nat(24);
                    v___x_1609_ = l_Lean_Exception_toMessageData(v_a_1600_);
                    v___f_1610_ = leanh::lean_alloc_closure(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    leanh::lean_closure_set(v___f_1610_, 0, v___x_1609_);
                    v___x_1611_ = leanh::lean_alloc_closure(
                        l_EIO_toBaseIO___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___x_1611_, 0, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_1611_, 1, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_1611_, 2, v___f_1610_);
                    v___x_1612_ = l_unsafeBaseIO___redArg(v___x_1611_);
                    if leanh::lean_obj_tag(v___x_1612_) == 0 {
                        v_a_1613_ = leanh::lean_ctor_get(v___x_1612_, 0);
                        leanh::lean_inc(v_a_1613_);
                        leanh::lean_dec_ref_known(v___x_1612_, 1);
                        v___x_1614_ = lean_io_error_to_string(v_a_1613_);
                        v___y_1606_ = v___x_1614_;
                        state = 5;
                        continue;
                    } else {
                        v_a_1615_ = leanh::lean_ctor_get(v___x_1612_, 0);
                        leanh::lean_inc(v_a_1615_);
                        leanh::lean_dec_ref_known(v___x_1612_, 1);
                        v___y_1606_ = v_a_1615_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_1616_ = leanh::lean_ctor_get(v___x_1599_, 0);
                    leanh::lean_inc(v_a_1616_);
                    leanh::lean_dec_ref_known(v___x_1599_, 1);
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
                leanh::lean_dec_ref(v___y_1606_);
                v___x_1608_ = l_panic___redArg(v_inst_1537_, v___x_1607_);
                return v___x_1608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg___boxed(
    mut v_inst_1623_: *mut leanh::LeanObject,
    mut v_env_1624_: *mut leanh::LeanObject,
    mut v_x_1625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1626_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(v_inst_1623_, v_env_1624_, v_x_1625_);
    leanh::lean_dec(v_inst_1623_);
    return v_res_1626_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM(
    mut v_00_u03b1_1627_: *mut leanh::LeanObject,
    mut v_inst_1628_: *mut leanh::LeanObject,
    mut v_env_1629_: *mut leanh::LeanObject,
    mut v_x_1630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1631_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(v_inst_1628_, v_env_1629_, v_x_1630_);
    return v___x_1631_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___boxed(
    mut v_00_u03b1_1632_: *mut leanh::LeanObject,
    mut v_inst_1633_: *mut leanh::LeanObject,
    mut v_env_1634_: *mut leanh::LeanObject,
    mut v_x_1635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1636_ =
        l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM(
            v_00_u03b1_1632_,
            v_inst_1633_,
            v_env_1634_,
            v_x_1635_,
        );
    leanh::lean_dec(v_inst_1633_);
    return v_res_1636_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0(
    mut v___y_1637_: *mut leanh::LeanObject,
    mut v___y_1638_: *mut leanh::LeanObject,
    mut v___y_1639_: *mut leanh::LeanObject,
    mut v___y_1640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1646_: u8 = 0;
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1653_: u8 = 0;
    let mut v_a_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1657_: u8 = 0;
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1661_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1642_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_cachedLocalSymbolFrequencyMap(v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
                if leanh::lean_obj_tag(v___x_1642_) == 0 {
                    v_a_1643_ = leanh::lean_ctor_get(v___x_1642_, 0);
                    v_isSharedCheck_1653_ = (!leanh::lean_is_exclusive(v___x_1642_)) as u8;
                    if v_isSharedCheck_1653_ == 0 {
                        v___x_1645_ = v___x_1642_;
                        v_isShared_1646_ = v_isSharedCheck_1653_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1643_);
                        leanh::lean_dec(v___x_1642_);
                        v___x_1645_ = leanh::lean_box(0);
                        v_isShared_1646_ = v_isSharedCheck_1653_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1654_ = leanh::lean_ctor_get(v___x_1642_, 0);
                    v_isSharedCheck_1661_ = (!leanh::lean_is_exclusive(v___x_1642_)) as u8;
                    if v_isSharedCheck_1661_ == 0 {
                        v___x_1656_ = v___x_1642_;
                        v_isShared_1657_ = v_isSharedCheck_1661_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1654_);
                        leanh::lean_dec(v___x_1642_);
                        v___x_1656_ = leanh::lean_box(0);
                        v_isShared_1657_ = v_isSharedCheck_1661_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1647_ = leanh::lean_unsigned_to_nat(1);
                v___x_1648_ = lean_mk_empty_array_with_capacity(v___x_1647_);
                v___x_1649_ = lean_array_push(v___x_1648_, v_a_1643_);
                if v_isShared_1646_ == 0 {
                    leanh::lean_ctor_set(v___x_1645_, 0, v___x_1649_);
                    v___x_1651_ = v___x_1645_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1652_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
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
                    v_reuseFailAlloc_1660_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
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
    mut v___y_1662_: *mut leanh::LeanObject,
    mut v___y_1663_: *mut leanh::LeanObject,
    mut v___y_1664_: *mut leanh::LeanObject,
    mut v___y_1665_: *mut leanh::LeanObject,
    mut v___y_1666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1667_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___lam__0(v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
    leanh::lean_dec(v___y_1665_);
    leanh::lean_dec_ref(v___y_1664_);
    leanh::lean_dec(v___y_1663_);
    leanh::lean_dec_ref(v___y_1662_);
    return v_res_1667_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1669_ = l_Array_instInhabited(leanh::lean_box(0));
    return v___x_1669_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3(
    mut v_env_1670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ents_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1671_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__0;
    v___x_1672_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1_once), _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3___closed__1);
    v_ents_1673_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(v___x_1672_, v_env_1670_, v___f_1671_);
    leanh::lean_inc_n(v_ents_1673_, 2);
    v___x_1674_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1674_, 0, v_ents_1673_);
    leanh::lean_ctor_set(v___x_1674_, 1, v_ents_1673_);
    leanh::lean_ctor_set(v___x_1674_, 2, v_ents_1673_);
    return v___x_1674_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(
    mut v_x_1677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1678_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_;
    return v___x_1678_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(
    mut v_x_1679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1680_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v_x_1679_);
    leanh::lean_dec_ref(v_x_1679_);
    return v_res_1680_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(
    mut v_x_1684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1685_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_;
    return v___x_1685_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(
    mut v_x_1686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1687_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v_x_1686_);
    leanh::lean_dec_ref(v_x_1686_);
    return v_res_1687_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(
    mut v_env_1688_: *mut leanh::LeanObject,
    mut v_x_1689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1690_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt_unsafe__3(v_env_1688_);
    return v___x_1690_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(
    mut v_env_1691_: *mut leanh::LeanObject,
    mut v_x_1692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1693_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v_env_1691_, v_x_1692_);
    leanh::lean_dec_ref(v_x_1692_);
    return v_res_1693_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(
    mut v_a_1694_: *mut leanh::LeanObject,
    mut v_a_1695_: u8,
) -> *mut leanh::LeanObject {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(
    mut v_a_1696_: *mut leanh::LeanObject,
    mut v_a_1697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_110__boxed_1698_: u8 = 0;
    let mut v_res_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_110__boxed_1698_ = (leanh::lean_unbox(v_a_1697_) as u8);
    v_res_1699_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v_a_1696_, v_a_110__boxed_1698_);
    leanh::lean_dec_ref(v_a_1696_);
    return v_res_1699_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(
    mut v_mapss_1700_: *mut leanh::LeanObject,
    mut v_x_1701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1703_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1703_, 0, v_mapss_1700_);
    return v___x_1703_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(
    mut v_mapss_1704_: *mut leanh::LeanObject,
    mut v_x_1705_: *mut leanh::LeanObject,
    mut v___y_1706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1707_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v_mapss_1704_, v_x_1705_);
    leanh::lean_dec_ref(v_x_1705_);
    return v_res_1707_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(
    mut v___x_1708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1710_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1710_, 0, v___x_1708_);
    return v___x_1710_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(
    mut v___x_1711_: *mut leanh::LeanObject,
    mut v___y_1712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1713_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_(v___x_1711_);
    return v_res_1713_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1738_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_;
    v___x_1739_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1738_);
    return v___x_1739_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2____boxed(
    mut v_a_1740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1741_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_();
    return v_res_1741_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1743_ = leanh::lean_box(0);
    v___x_1744_ = lean_st_mk_ref(v___x_1743_);
    v___x_1745_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1745_, 0, v___x_1744_);
    return v___x_1745_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2____boxed(
    mut v_a_1746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1747_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2_();
    return v_res_1747_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instZeroNameMapNat()
-> *mut leanh::LeanObject {
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1748_ = leanh::lean_box(1);
    return v___x_1748_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0(
    mut v___x_1749_: *mut leanh::LeanObject,
    mut v_x_x27_1750_: *mut leanh::LeanObject,
    mut v_n_1751_: *mut leanh::LeanObject,
    mut v_c_1752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1753_ = leanh::lean_unsigned_to_nat(0);
    leanh::lean_inc(v_n_1751_);
    leanh::lean_inc(v_x_x27_1750_);
    v___x_1754_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(
        v___x_1749_,
        v_x_x27_1750_,
        v_n_1751_,
        v___x_1753_,
    );
    v___x_1755_ = lean_nat_add(v___x_1754_, v_c_1752_);
    leanh::lean_dec(v___x_1754_);
    v___x_1756_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_n_1751_,
        v___x_1755_,
        v_x_x27_1750_,
    );
    return v___x_1756_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0___boxed(
    mut v___x_1757_: *mut leanh::LeanObject,
    mut v_x_x27_1758_: *mut leanh::LeanObject,
    mut v_n_1759_: *mut leanh::LeanObject,
    mut v_c_1760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1761_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__0(v___x_1757_, v_x_x27_1758_, v_n_1759_, v_c_1760_);
    leanh::lean_dec(v_c_1760_);
    return v_res_1761_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1(
    mut v_x_1765_: *mut leanh::LeanObject,
    mut v_y_1766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1767_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instAddNameMapNat___lam__1___closed__1;
    v___x_1768_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1767_, v_x_1765_, v_y_1766_);
    return v___x_1768_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(
    mut v_init_1771_: *mut leanh::LeanObject,
    mut v_x_1772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1772_) == 0 {
                    v_k_1773_ = leanh::lean_ctor_get(v_x_1772_, 1);
                    leanh::lean_inc(v_k_1773_);
                    v_v_1774_ = leanh::lean_ctor_get(v_x_1772_, 2);
                    leanh::lean_inc(v_v_1774_);
                    v_l_1775_ = leanh::lean_ctor_get(v_x_1772_, 3);
                    leanh::lean_inc(v_l_1775_);
                    v_r_1776_ = leanh::lean_ctor_get(v_x_1772_, 4);
                    leanh::lean_inc(v_r_1776_);
                    leanh::lean_dec_ref_known(v_x_1772_, 5);
                    v___x_1777_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(v_init_1771_, v_l_1775_);
                    v___x_1778_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1779_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v___x_1777_, v_k_1773_, v___x_1778_);
                    v___x_1780_ = lean_nat_add(v___x_1779_, v_v_1774_);
                    leanh::lean_dec(v_v_1774_);
                    leanh::lean_dec(v___x_1779_);
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
    mut v_as_1783_: *mut leanh::LeanObject,
    mut v_i_1784_: usize,
    mut v_stop_1785_: usize,
    mut v_b_1786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1787_: u8 = 0;
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: usize = 0;
    let mut v___x_1791_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1787_ = lean_usize_dec_eq(v_i_1784_, v_stop_1785_);
                if v___x_1787_ == 0 {
                    v___x_1788_ = lean_array_uget_borrowed(v_as_1783_, v_i_1784_);
                    leanh::lean_inc(v___x_1788_);
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
    mut v_as_1793_: *mut leanh::LeanObject,
    mut v_i_1794_: *mut leanh::LeanObject,
    mut v_stop_1795_: *mut leanh::LeanObject,
    mut v_b_1796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1797_: usize = 0;
    let mut v_stop_boxed_1798_: usize = 0;
    let mut v_res_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1797_ = leanh::lean_unbox_usize(v_i_1794_);
    leanh::lean_dec(v_i_1794_);
    v_stop_boxed_1798_ = leanh::lean_unbox_usize(v_stop_1795_);
    leanh::lean_dec(v_stop_1795_);
    v_res_1799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(v_as_1793_, v_i_boxed_1797_, v_stop_boxed_1798_, v_b_1796_);
    leanh::lean_dec_ref(v_as_1793_);
    return v_res_1799_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(
    mut v_as_1800_: *mut leanh::LeanObject,
    mut v_i_1801_: usize,
    mut v_stop_1802_: usize,
    mut v_b_1803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: usize = 0;
    let mut v___x_1807_: usize = 0;
    let mut v___x_1809_: u8 = 0;
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: u8 = 0;
    let mut v___x_1814_: u8 = 0;
    let mut v___x_1815_: usize = 0;
    let mut v___x_1816_: usize = 0;
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: usize = 0;
    let mut v___x_1819_: usize = 0;
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1809_ = lean_usize_dec_eq(v_i_1801_, v_stop_1802_);
                if v___x_1809_ == 0 {
                    v___x_1810_ = lean_array_uget_borrowed(v_as_1800_, v_i_1801_);
                    v___x_1811_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_as_1821_: *mut leanh::LeanObject,
    mut v_i_1822_: *mut leanh::LeanObject,
    mut v_stop_1823_: *mut leanh::LeanObject,
    mut v_b_1824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1825_: usize = 0;
    let mut v_stop_boxed_1826_: usize = 0;
    let mut v_res_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1825_ = leanh::lean_unbox_usize(v_i_1822_);
    leanh::lean_dec(v_i_1822_);
    v_stop_boxed_1826_ = leanh::lean_unbox_usize(v_stop_1823_);
    leanh::lean_dec(v_stop_1823_);
    v_res_1827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(v_as_1821_, v_i_boxed_1825_, v_stop_boxed_1826_, v_b_1824_);
    leanh::lean_dec_ref(v_as_1821_);
    return v_res_1827_;
}
pub unsafe fn _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1828_ = l_Array_instInhabited(leanh::lean_box(0));
    return v___x_1828_;
}
pub unsafe fn l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(
    mut v_a_1829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: u8 = 0;
    let mut v___x_1850_: u8 = 0;
    let mut v___x_1851_: usize = 0;
    let mut v___x_1852_: usize = 0;
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: usize = 0;
    let mut v___x_1855_: usize = 0;
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1860_: u8 = 0;
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1864_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1831_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyMapRef;
                v___x_1832_ = lean_st_ref_get(v___x_1831_);
                if leanh::lean_obj_tag(v___x_1832_) == 0 {
                    v___x_1833_ = lean_st_ref_get(v_a_1829_);
                    v_env_1839_ = leanh::lean_ctor_get(v___x_1833_, 0);
                    leanh::lean_inc_ref(v_env_1839_);
                    leanh::lean_dec(v___x_1833_);
                    v___x_1840_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt;
                    v_toEnvExtension_1841_ = leanh::lean_ctor_get(v___x_1840_, 0);
                    v_asyncMode_1842_ = leanh::lean_ctor_get(v_toEnvExtension_1841_, 2);
                    v___x_1843_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0_once
                        ),
                        _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg___closed__0,
                    );
                    v___x_1844_ = leanh::lean_box(0);
                    v___x_1845_ = l_Lean_PersistentEnvExtension_getState___redArg(
                        v___x_1843_,
                        v___x_1840_,
                        v_env_1839_,
                        v_asyncMode_1842_,
                        v___x_1844_,
                    );
                    v___x_1846_ = leanh::lean_box(1);
                    v___x_1847_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1848_ = lean_array_get_size(v___x_1845_);
                    v___x_1849_ = lean_nat_dec_lt(v___x_1847_, v___x_1848_);
                    if v___x_1849_ == 0 {
                        leanh::lean_dec(v___x_1845_);
                        v___y_1835_ = v___x_1846_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1850_ = lean_nat_dec_le(v___x_1848_, v___x_1848_);
                        if v___x_1850_ == 0 {
                            if v___x_1849_ == 0 {
                                leanh::lean_dec(v___x_1845_);
                                v___y_1835_ = v___x_1846_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1851_ = 0usize;
                                v___x_1852_ = lean_usize_of_nat(v___x_1848_);
                                v___x_1853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(v___x_1845_, v___x_1851_, v___x_1852_, v___x_1846_);
                                leanh::lean_dec(v___x_1845_);
                                v___y_1835_ = v___x_1853_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_1854_ = 0usize;
                            v___x_1855_ = lean_usize_of_nat(v___x_1848_);
                            v___x_1856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(v___x_1845_, v___x_1854_, v___x_1855_, v___x_1846_);
                            leanh::lean_dec(v___x_1845_);
                            v___y_1835_ = v___x_1856_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_val_1857_ = leanh::lean_ctor_get(v___x_1832_, 0);
                    v_isSharedCheck_1864_ = (!leanh::lean_is_exclusive(v___x_1832_)) as u8;
                    if v_isSharedCheck_1864_ == 0 {
                        v___x_1859_ = v___x_1832_;
                        v_isShared_1860_ = v_isSharedCheck_1864_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1857_);
                        leanh::lean_dec(v___x_1832_);
                        v___x_1859_ = leanh::lean_box(0);
                        v_isShared_1860_ = v_isSharedCheck_1864_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___y_1835_);
                v___x_1836_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1836_, 0, v___y_1835_);
                v___x_1837_ = lean_st_ref_set(v___x_1831_, v___x_1836_);
                v___x_1838_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1838_, 0, v___y_1835_);
                return v___x_1838_;
            }
            2 => {
                if v_isShared_1860_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1859_, 0);
                    v___x_1862_ = v___x_1859_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1863_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_val_1857_);
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
    mut v_a_1865_: *mut leanh::LeanObject,
    mut v_a_1866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1867_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(v_a_1865_);
    leanh::lean_dec(v_a_1865_);
    return v_res_1867_;
}
pub unsafe fn l_Lean_LibrarySuggestions_symbolFrequencyMap(
    mut v_a_1868_: *mut leanh::LeanObject,
    mut v_a_1869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1871_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(v_a_1869_);
    return v___x_1871_;
}
pub unsafe fn l_Lean_LibrarySuggestions_symbolFrequencyMap___boxed(
    mut v_a_1872_: *mut leanh::LeanObject,
    mut v_a_1873_: *mut leanh::LeanObject,
    mut v_a_1874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1875_ = l_Lean_LibrarySuggestions_symbolFrequencyMap(v_a_1872_, v_a_1873_);
    leanh::lean_dec(v_a_1873_);
    leanh::lean_dec_ref(v_a_1872_);
    return v_res_1875_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0(
    mut v_init_1876_: *mut leanh::LeanObject,
    mut v_t_1877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1878_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0_spec__0(v_init_1876_, v_t_1877_);
    return v___x_1878_;
}
pub unsafe fn l_Lean_LibrarySuggestions_symbolFrequency___redArg(
    mut v_n_1879_: *mut leanh::LeanObject,
    mut v_a_1880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1886_: u8 = 0;
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1892_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1882_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(v_a_1880_);
                v_a_1883_ = leanh::lean_ctor_get(v___x_1882_, 0);
                v_isSharedCheck_1892_ = (!leanh::lean_is_exclusive(v___x_1882_)) as u8;
                if v_isSharedCheck_1892_ == 0 {
                    v___x_1885_ = v___x_1882_;
                    v_isShared_1886_ = v_isSharedCheck_1892_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1883_);
                    leanh::lean_dec(v___x_1882_);
                    v___x_1885_ = leanh::lean_box(0);
                    v_isShared_1886_ = v_isSharedCheck_1892_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1887_ = leanh::lean_unsigned_to_nat(0);
                v___x_1888_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_a_1883_, v_n_1879_, v___x_1887_);
                leanh::lean_dec(v_a_1883_);
                if v_isShared_1886_ == 0 {
                    leanh::lean_ctor_set(v___x_1885_, 0, v___x_1888_);
                    v___x_1890_ = v___x_1885_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1891_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
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
    mut v_n_1893_: *mut leanh::LeanObject,
    mut v_a_1894_: *mut leanh::LeanObject,
    mut v_a_1895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1896_ = l_Lean_LibrarySuggestions_symbolFrequency___redArg(v_n_1893_, v_a_1894_);
    leanh::lean_dec(v_a_1894_);
    leanh::lean_dec(v_n_1893_);
    return v_res_1896_;
}
pub unsafe fn l_Lean_LibrarySuggestions_symbolFrequency(
    mut v_n_1897_: *mut leanh::LeanObject,
    mut v_a_1898_: *mut leanh::LeanObject,
    mut v_a_1899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1901_ = l_Lean_LibrarySuggestions_symbolFrequency___redArg(v_n_1897_, v_a_1899_);
    return v___x_1901_;
}
pub unsafe fn l_Lean_LibrarySuggestions_symbolFrequency___boxed(
    mut v_n_1902_: *mut leanh::LeanObject,
    mut v_a_1903_: *mut leanh::LeanObject,
    mut v_a_1904_: *mut leanh::LeanObject,
    mut v_a_1905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1906_ = l_Lean_LibrarySuggestions_symbolFrequency(v_n_1902_, v_a_1903_, v_a_1904_);
    leanh::lean_dec(v_a_1904_);
    leanh::lean_dec_ref(v_a_1903_);
    leanh::lean_dec(v_n_1902_);
    return v_res_1906_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_LibrarySuggestions_SymbolFrequency(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_LibrarySuggestions_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_224017424____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_localSymbolFrequencyMapRef = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_localSymbolFrequencyMapRef);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_3575993952____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyExt);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_2997076389____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyMapRef = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyMapRef);
    leanh::lean_dec_ref(res);
    l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instZeroNameMapNat = _init_l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instZeroNameMapNat();
    leanh::lean_mark_persistent(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_instZeroNameMapNat);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_LibrarySuggestions_SymbolFrequency(
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
pub unsafe fn initialize_Lean_LibrarySuggestions_SymbolFrequency(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_LibrarySuggestions_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
}
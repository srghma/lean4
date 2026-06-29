// Lean compiler output
// Module: Lean.Compiler.LCNF.PhaseExt
// Imports: Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.PublicDeclsExt
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::BinSearch::l_Array_binSearchAux___redArg;
use crate::r#gen::Init::Data::Nat::Power2::Basic::l_Nat_nextPowerOfTwo;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed, l_Lean_mkAtom,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_id___boxed, l_instInhabitedForall___redArg___lam__0___boxed, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l_Lean_Compiler_LCNF_instInhabitedDecl_default,
    l_Lean_Compiler_LCNF_instInhabitedSignature_default,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l_Lean_Compiler_LCNF_Phase_toPurity, l_Lean_Compiler_LCNF_getPhase___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    initialize_Lean_Compiler_LCNF_PassManager, l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg,
    runtime_initialize_Lean_Compiler_LCNF_PassManager,
};
use crate::r#gen::Lean::Compiler::LCNF::PublicDeclsExt::{
    initialize_Lean_Compiler_LCNF_PublicDeclsExt, l_Lean_Compiler_LCNF_isDeclPublic,
    l_Lean_Compiler_LCNF_mkOrderedDeclSetExt, runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_quickLt;
use crate::r#gen::Lean::Data::NameMap::Basic::{l_Lean_NameSet_contains, l_Lean_NameSet_insert};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg, l_Lean_PersistentHashMap_instInhabited,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1,
    l_Lean_EnvExtension_modifyState___redArg, l_Lean_Environment_getModuleIdxFor_x3f,
    l_Lean_Environment_header, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getModuleEntries___redArg,
    l_Lean_PersistentEnvExtension_getState___redArg, l_Lean_instInhabitedEnvExtension_default,
    l_Lean_registerEnvExtension___redArg, l_Lean_registerPersistentEnvExtensionUnsafe___redArg,
};
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::ffi::{
    lean_array_fswap, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_array,
};
use crate::ffi::lean_array_fset;
use crate::ffi::lean_nat_shiftr;
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_baseTransparentDeclsExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_monoTransparentDeclsExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_impureTransparentDeclsExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_isDeclTransparent___closed__0_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_isDeclTransparent___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_isDeclTransparent___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__1_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 108, 111, 99, 97, 108, 32, 101, 110, 116, 114, 105, 101, 115, 58, 32, 0]};
static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_id___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        40, 96, 73, 110, 104, 97, 98, 105, 116, 101, 100, 46, 100, 101, 102, 97, 117, 108, 116, 96,
        32, 102, 111, 114, 32, 96, 73, 79, 46, 69, 114, 114, 111, 114, 96, 41, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 18,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0_value:
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
static mut l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__1_value:
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
    m_fun: l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__2_value:
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
    m_fun: l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__3_value:
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
    m_fun: l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value:
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
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1_value:
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
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__2_value:
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
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__3_value:
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
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5_value:
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
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__6_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__6_value)
            as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__8_value:
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
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__8_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__10_value:
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
    m_data: [101, 120, 97, 99, 116, 0],
};
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__10_value)
            as *mut crate::leanh::LeanObject,
        14997215300048349804 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__14_value:
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
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__15_value:
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
    m_data: [100, 101, 99, 108, 78, 97, 109, 101, 0],
};
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__15_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__14_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__15_value)
            as *mut crate::leanh::LeanObject,
        7677164612348466033 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__17_value:
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
    m_data: [100, 101, 99, 108, 95, 110, 97, 109, 101, 37, 0],
};
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_mkDeclExt___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [((( 3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkDeclExt___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Compiler_LCNF_mkDeclExt___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkDeclExt___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Compiler_LCNF_mkDeclExt___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkDeclExt___closed__2_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Compiler_LCNF_mkDeclExt___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_mkDeclExt___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_mkDeclExt___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_mkDeclExt___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_mkDeclExt___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkDeclExt___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [98, 97, 115, 101, 69, 120, 116, 0]};
static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8543197020067251012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13270991020494245093 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2789893139926998929 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_baseExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [109, 111, 110, 111, 69, 120, 116, 0]};
static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8543197020067251012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13270991020494245093 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13503844699047413665 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_monoExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 2, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_impureExt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0_value:
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
static mut l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__1_value:
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
    m_fun: l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__2_value:
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
    m_fun: l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__3_value:
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
    m_fun: l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_id___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_mkSigDeclExt___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_mkSigDeclExt___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Compiler_LCNF_mkSigDeclExt___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_mkSigDeclExt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkSigDeclExt___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_mkSigDeclExt___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkSigDeclExt___closed__2_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_mkSigDeclExt___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkSigDeclExt___closed__3_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_mkSigDeclExt___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [105, 109, 112, 117, 114, 101, 83, 105, 103, 69, 120, 116, 0]};
static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8543197020067251012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13270991020494245093 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17119251738815796981 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_impureSigExt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__1_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_getSigCore_x3f___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getSigCore_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___lam__0 as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Decl_save___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Decl_save___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Decl_save___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Decl_save___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Decl_save___closed__2_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_Decl_save___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_save___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_save___closed__3_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_Decl_save___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_save___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__0_value: crate::leanh::LeanStringObject<
    67,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 67,
    m_capacity: 67,
    m_length: 66,
    m_data: [
        73, 110, 116, 101, 114, 110, 97, 108, 32, 99, 111, 109, 112, 105, 108, 101, 114, 32, 101,
        114, 114, 111, 114, 58, 32, 103, 101, 116, 68, 101, 99, 108, 63, 32, 111, 110, 32, 105,
        109, 112, 117, 114, 101, 32, 105, 115, 32, 117, 110, 117, 115, 112, 112, 111, 114, 116,
        101, 100, 32, 102, 111, 114, 32, 110, 111, 119, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_declOrderExt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__0_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 80, 104, 97, 115, 101, 69, 120, 116, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__1_value: crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 103, 101, 116, 73, 109, 112, 117, 114, 101, 68, 101, 99, 108, 73, 110, 100, 105, 99, 101, 115, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__2_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 105, 32, 33, 61, 32, 48, 10, 32, 32, 32, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__2_value:
    crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 109, 97, 112, 46, 115, 105, 122, 101, 32, 61, 61, 32, 116, 97, 114, 103, 101, 116,
        115, 46, 115, 105, 122, 101, 10, 32, 32, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3496178540____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2965_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
    return v___x_2965_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3496178540____hygCtx___hyg_2____boxed(
    mut v_a_2966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2967_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3496178540____hygCtx___hyg_2_();
    return v_res_2967_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1977385844____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2969_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
    return v___x_2969_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1977385844____hygCtx___hyg_2____boxed(
    mut v_a_2970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2971_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1977385844____hygCtx___hyg_2_();
    return v_res_2971_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_975450157____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2973_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
    return v___x_2973_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_975450157____hygCtx___hyg_2____boxed(
    mut v_a_2974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2975_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_975450157____hygCtx___hyg_2_();
    return v_res_2975_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_getTransparencyExt(
    mut v_x_2976_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_2976_ {
        0 => {
            let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2977_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_baseTransparentDeclsExt;
            return v___x_2977_;
        }
        1 => {
            let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2978_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_monoTransparentDeclsExt;
            return v___x_2978_;
        }
        _ => {
            let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2979_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_impureTransparentDeclsExt;
            return v___x_2979_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_getTransparencyExt___boxed(
    mut v_x_2980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_25__boxed_2981_: u8 = 0;
    let mut v_res_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_25__boxed_2981_ = (crate::leanh::lean_unbox(v_x_2980_) as u8);
    v_res_2982_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_getTransparencyExt(
        v_x_25__boxed_2981_,
    );
    return v_res_2982_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isDeclTransparent(
    mut v_env_2986_: *mut crate::leanh::LeanObject,
    mut v_phase_2987_: u8,
    mut v_declName_2988_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_2990_: u8 = 0;
    v___x_2989_ = l_Lean_Environment_header(v_env_2986_);
    v_isModule_2990_ = crate::leanh::lean_ctor_get_uint8(
        v___x_2989_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 4) as u32,
    );
    crate::leanh::lean_dec_ref(v___x_2989_);
    if v_isModule_2990_ == 0 {
        let mut v___x_2991_: u8 = 0;
        crate::leanh::lean_dec_ref(v_env_2986_);
        v___x_2991_ = 1;
        return v___x_2991_;
    } else {
        let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_asyncMode_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2998_: u8 = 0;
        v___x_2992_ =
            l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_getTransparencyExt(
                v_phase_2987_,
            );
        v_asyncMode_2993_ = crate::leanh::lean_ctor_get(v___x_2992_, 2);
        crate::leanh::lean_inc(v_asyncMode_2993_);
        v___x_2994_ = l_Lean_Compiler_LCNF_isDeclTransparent___closed__0;
        v___x_2995_ = crate::leanh::lean_box(0);
        v___x_2996_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
            v___x_2994_,
            v___x_2992_,
            v_env_2986_,
            v_asyncMode_2993_,
            v___x_2995_,
        );
        crate::leanh::lean_dec(v_asyncMode_2993_);
        crate::leanh::lean_dec_ref(v___x_2992_);
        v_snd_2997_ = crate::leanh::lean_ctor_get(v___x_2996_, 1);
        crate::leanh::lean_inc(v_snd_2997_);
        crate::leanh::lean_dec(v___x_2996_);
        v___x_2998_ = l_Lean_NameSet_contains(v_snd_2997_, v_declName_2988_);
        crate::leanh::lean_dec(v_snd_2997_);
        return v___x_2998_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_isDeclTransparent___boxed(
    mut v_env_2999_: *mut crate::leanh::LeanObject,
    mut v_phase_3000_: *mut crate::leanh::LeanObject,
    mut v_declName_3001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_3002_: u8 = 0;
    let mut v_res_3003_: u8 = 0;
    let mut v_r_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_3002_ = (crate::leanh::lean_unbox(v_phase_3000_) as u8);
    v_res_3003_ =
        l_Lean_Compiler_LCNF_isDeclTransparent(v_env_2999_, v_phase_boxed_3002_, v_declName_3001_);
    crate::leanh::lean_dec(v_declName_3001_);
    v_r_3004_ = crate::leanh::lean_box((v_res_3003_) as usize);
    return v_r_3004_;
}
pub unsafe fn l_Lean_Compiler_LCNF_setDeclTransparent___lam__0(
    mut v_declName_3005_: *mut crate::leanh::LeanObject,
    mut v_s_3006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3011_: u8 = 0;
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3007_ = crate::leanh::lean_ctor_get(v_s_3006_, 0);
                v_snd_3008_ = crate::leanh::lean_ctor_get(v_s_3006_, 1);
                v_isSharedCheck_3017_ = (!crate::leanh::lean_is_exclusive(v_s_3006_)) as u8;
                if v_isSharedCheck_3017_ == 0 {
                    v___x_3010_ = v_s_3006_;
                    v_isShared_3011_ = v_isSharedCheck_3017_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3008_);
                    crate::leanh::lean_inc(v_fst_3007_);
                    crate::leanh::lean_dec(v_s_3006_);
                    v___x_3010_ = crate::leanh::lean_box(0);
                    v_isShared_3011_ = v_isSharedCheck_3017_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_declName_3005_);
                v___x_3012_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3012_, 0, v_declName_3005_);
                crate::leanh::lean_ctor_set(v___x_3012_, 1, v_fst_3007_);
                v___x_3013_ = l_Lean_NameSet_insert(v_snd_3008_, v_declName_3005_);
                if v_isShared_3011_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3010_, 1, v___x_3013_);
                    crate::leanh::lean_ctor_set(v___x_3010_, 0, v___x_3012_);
                    v___x_3015_ = v___x_3010_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3016_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3012_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 1, v___x_3013_);
                    v___x_3015_ = v_reuseFailAlloc_3016_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3015_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_setDeclTransparent(
    mut v_env_3018_: *mut crate::leanh::LeanObject,
    mut v_phase_3019_: u8,
    mut v_declName_3020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3021_: u8 = 0;
    crate::leanh::lean_inc_ref(v_env_3018_);
    v___x_3021_ =
        l_Lean_Compiler_LCNF_isDeclTransparent(v_env_3018_, v_phase_3019_, v_declName_3020_);
    if v___x_3021_ == 0 {
        let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_asyncMode_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3022_ =
            l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_getTransparencyExt(
                v_phase_3019_,
            );
        v_asyncMode_3023_ = crate::leanh::lean_ctor_get(v___x_3022_, 2);
        crate::leanh::lean_inc(v_asyncMode_3023_);
        v___f_3024_ = crate::leanh::lean_alloc_closure(
            l_Lean_Compiler_LCNF_setDeclTransparent___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_3024_, 0, v_declName_3020_);
        v___x_3025_ = crate::leanh::lean_box(0);
        v___x_3026_ = l_Lean_EnvExtension_modifyState___redArg(
            v___x_3022_,
            v_env_3018_,
            v___f_3024_,
            v_asyncMode_3023_,
            v___x_3025_,
        );
        crate::leanh::lean_dec(v_asyncMode_3023_);
        return v___x_3026_;
    } else {
        crate::leanh::lean_dec(v_declName_3020_);
        return v_env_3018_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_setDeclTransparent___boxed(
    mut v_env_3027_: *mut crate::leanh::LeanObject,
    mut v_phase_3028_: *mut crate::leanh::LeanObject,
    mut v_declName_3029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_3030_: u8 = 0;
    let mut v_res_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_3030_ = (crate::leanh::lean_unbox(v_phase_3028_) as u8);
    v_res_3031_ =
        l_Lean_Compiler_LCNF_setDeclTransparent(v_env_3027_, v_phase_boxed_3030_, v_declName_3029_);
    return v_res_3031_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___lam__0(
    mut v_ps_3032_: *mut crate::leanh::LeanObject,
    mut v_x_3033_: *mut crate::leanh::LeanObject,
    mut v_v_3034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3035_ = lean_array_push(v_ps_3032_, v_v_3034_);
    return v___x_3035_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___lam__0___boxed(
    mut v_ps_3036_: *mut crate::leanh::LeanObject,
    mut v_x_3037_: *mut crate::leanh::LeanObject,
    mut v_v_3038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3039_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___lam__0(v_ps_3036_, v_x_3037_, v_v_3038_);
    crate::leanh::lean_dec(v_x_3037_);
    return v_res_3039_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_f_3040_: *mut crate::leanh::LeanObject,
    mut v_keys_3041_: *mut crate::leanh::LeanObject,
    mut v_vals_3042_: *mut crate::leanh::LeanObject,
    mut v_i_3043_: *mut crate::leanh::LeanObject,
    mut v_acc_3044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: u8 = 0;
    let mut v_k_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3045_ = lean_array_get_size(v_keys_3041_);
                v___x_3046_ = lean_nat_dec_lt(v_i_3043_, v___x_3045_);
                if v___x_3046_ == 0 {
                    crate::leanh::lean_dec(v_i_3043_);
                    crate::leanh::lean_dec(v_f_3040_);
                    return v_acc_3044_;
                } else {
                    v_k_3047_ = lean_array_fget_borrowed(v_keys_3041_, v_i_3043_);
                    v_v_3048_ = lean_array_fget_borrowed(v_vals_3042_, v_i_3043_);
                    crate::leanh::lean_inc(v_f_3040_);
                    crate::leanh::lean_inc(v_v_3048_);
                    crate::leanh::lean_inc(v_k_3047_);
                    v___x_3049_ =
                        crate::leanh::lean_apply_3(v_f_3040_, v_acc_3044_, v_k_3047_, v_v_3048_);
                    v___x_3050_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3051_ = lean_nat_add(v_i_3043_, v___x_3050_);
                    crate::leanh::lean_dec(v_i_3043_);
                    v_i_3043_ = v___x_3051_;
                    v_acc_3044_ = v___x_3049_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_f_3053_: *mut crate::leanh::LeanObject,
    mut v_keys_3054_: *mut crate::leanh::LeanObject,
    mut v_vals_3055_: *mut crate::leanh::LeanObject,
    mut v_i_3056_: *mut crate::leanh::LeanObject,
    mut v_acc_3057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3058_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg(v_f_3053_, v_keys_3054_, v_vals_3055_, v_i_3056_, v_acc_3057_);
    crate::leanh::lean_dec_ref(v_vals_3055_);
    crate::leanh::lean_dec_ref(v_keys_3054_);
    return v_res_3058_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(
    mut v_f_3059_: *mut crate::leanh::LeanObject,
    mut v_x_3060_: *mut crate::leanh::LeanObject,
    mut v_x_3061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3060_) == 0 {
        let mut v_es_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3065_: u8 = 0;
        v_es_3062_ = crate::leanh::lean_ctor_get(v_x_3060_, 0);
        v___x_3063_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3064_ = lean_array_get_size(v_es_3062_);
        v___x_3065_ = lean_nat_dec_lt(v___x_3063_, v___x_3064_);
        if v___x_3065_ == 0 {
            crate::leanh::lean_dec(v_f_3059_);
            return v_x_3061_;
        } else {
            let mut v___x_3066_: u8 = 0;
            v___x_3066_ = lean_nat_dec_le(v___x_3064_, v___x_3064_);
            if v___x_3066_ == 0 {
                if v___x_3065_ == 0 {
                    crate::leanh::lean_dec(v_f_3059_);
                    return v_x_3061_;
                } else {
                    let mut v___x_3067_: usize = 0;
                    let mut v___x_3068_: usize = 0;
                    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_3067_ = 0usize;
                    v___x_3068_ = lean_usize_of_nat(v___x_3064_);
                    v___x_3069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3059_, v_es_3062_, v___x_3067_, v___x_3068_, v_x_3061_);
                    return v___x_3069_;
                }
            } else {
                let mut v___x_3070_: usize = 0;
                let mut v___x_3071_: usize = 0;
                let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3070_ = 0usize;
                v___x_3071_ = lean_usize_of_nat(v___x_3064_);
                v___x_3072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3059_, v_es_3062_, v___x_3070_, v___x_3071_, v_x_3061_);
                return v___x_3072_;
            }
        }
    } else {
        let mut v_ks_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ks_3073_ = crate::leanh::lean_ctor_get(v_x_3060_, 0);
        v_vs_3074_ = crate::leanh::lean_ctor_get(v_x_3060_, 1);
        v___x_3075_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3076_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg(v_f_3059_, v_ks_3073_, v_vs_3074_, v___x_3075_, v_x_3061_);
        return v___x_3076_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_f_3077_: *mut crate::leanh::LeanObject,
    mut v_as_3078_: *mut crate::leanh::LeanObject,
    mut v_i_3079_: usize,
    mut v_stop_3080_: usize,
    mut v_b_3081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: usize = 0;
    let mut v___x_3085_: usize = 0;
    let mut v___x_3087_: u8 = 0;
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3087_ = lean_usize_dec_eq(v_i_3079_, v_stop_3080_);
                if v___x_3087_ == 0 {
                    v___x_3088_ = lean_array_uget_borrowed(v_as_3078_, v_i_3079_);
                    match crate::leanh::lean_obj_tag(v___x_3088_) {
                        0 => {
                            v_key_3089_ = crate::leanh::lean_ctor_get(v___x_3088_, 0);
                            v_val_3090_ = crate::leanh::lean_ctor_get(v___x_3088_, 1);
                            crate::leanh::lean_inc(v_f_3077_);
                            crate::leanh::lean_inc(v_val_3090_);
                            crate::leanh::lean_inc(v_key_3089_);
                            v___x_3091_ = crate::leanh::lean_apply_3(
                                v_f_3077_,
                                v_b_3081_,
                                v_key_3089_,
                                v_val_3090_,
                            );
                            v___y_3083_ = v___x_3091_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_3092_ = crate::leanh::lean_ctor_get(v___x_3088_, 0);
                            crate::leanh::lean_inc(v_f_3077_);
                            v___x_3093_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_3077_, v_node_3092_, v_b_3081_);
                            v___y_3083_ = v___x_3093_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_3083_ = v_b_3081_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_f_3077_);
                    return v_b_3081_;
                }
            }
            1 => {
                v___x_3084_ = 1usize;
                v___x_3085_ = lean_usize_add(v_i_3079_, v___x_3084_);
                v_i_3079_ = v___x_3085_;
                v_b_3081_ = v___y_3083_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_f_3094_: *mut crate::leanh::LeanObject,
    mut v_as_3095_: *mut crate::leanh::LeanObject,
    mut v_i_3096_: *mut crate::leanh::LeanObject,
    mut v_stop_3097_: *mut crate::leanh::LeanObject,
    mut v_b_3098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3099_: usize = 0;
    let mut v_stop_boxed_3100_: usize = 0;
    let mut v_res_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3099_ = crate::leanh::lean_unbox_usize(v_i_3096_);
    crate::leanh::lean_dec(v_i_3096_);
    v_stop_boxed_3100_ = crate::leanh::lean_unbox_usize(v_stop_3097_);
    crate::leanh::lean_dec(v_stop_3097_);
    v_res_3101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3094_, v_as_3095_, v_i_boxed_3099_, v_stop_boxed_3100_, v_b_3098_);
    crate::leanh::lean_dec_ref(v_as_3095_);
    return v_res_3101_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_f_3102_: *mut crate::leanh::LeanObject,
    mut v_x_3103_: *mut crate::leanh::LeanObject,
    mut v_x_3104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3105_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_3102_, v_x_3103_, v_x_3104_);
    crate::leanh::lean_dec_ref(v_x_3103_);
    return v_res_3105_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg___lam__0(
    mut v_f_3106_: *mut crate::leanh::LeanObject,
    mut v_x1_3107_: *mut crate::leanh::LeanObject,
    mut v_x2_3108_: *mut crate::leanh::LeanObject,
    mut v_x3_3109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3110_ = crate::leanh::lean_apply_3(v_f_3106_, v_x1_3107_, v_x2_3108_, v_x3_3109_);
    return v___x_3110_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(
    mut v_map_3111_: *mut crate::leanh::LeanObject,
    mut v_f_3112_: *mut crate::leanh::LeanObject,
    mut v_init_3113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3114_ = crate::leanh::lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    crate::leanh::lean_closure_set(v___f_3114_, 0, v_f_3112_);
    v___x_3115_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v___f_3114_, v_map_3111_, v_init_3113_);
    return v___x_3115_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg___boxed(
    mut v_map_3116_: *mut crate::leanh::LeanObject,
    mut v_f_3117_: *mut crate::leanh::LeanObject,
    mut v_init_3118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3119_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_map_3116_, v_f_3117_, v_init_3118_);
    crate::leanh::lean_dec_ref(v_map_3116_);
    return v_res_3119_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___redArg(
    mut v_lt_3120_: *mut crate::leanh::LeanObject,
    mut v_hi_3121_: *mut crate::leanh::LeanObject,
    mut v_pivot_3122_: *mut crate::leanh::LeanObject,
    mut v_as_3123_: *mut crate::leanh::LeanObject,
    mut v_i_3124_: *mut crate::leanh::LeanObject,
    mut v_k_3125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3126_: u8 = 0;
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: u8 = 0;
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3126_ = lean_nat_dec_lt(v_k_3125_, v_hi_3121_);
                if v___x_3126_ == 0 {
                    crate::leanh::lean_dec(v_k_3125_);
                    crate::leanh::lean_dec(v_pivot_3122_);
                    crate::leanh::lean_dec_ref(v_lt_3120_);
                    v___x_3127_ = lean_array_fswap(v_as_3123_, v_i_3124_, v_hi_3121_);
                    v___x_3128_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3128_, 0, v_i_3124_);
                    crate::leanh::lean_ctor_set(v___x_3128_, 1, v___x_3127_);
                    return v___x_3128_;
                } else {
                    v___x_3129_ = lean_array_fget_borrowed(v_as_3123_, v_k_3125_);
                    crate::leanh::lean_inc_ref(v_lt_3120_);
                    crate::leanh::lean_inc(v_pivot_3122_);
                    crate::leanh::lean_inc(v___x_3129_);
                    v___x_3130_ =
                        crate::leanh::lean_apply_2(v_lt_3120_, v___x_3129_, v_pivot_3122_);
                    v___x_3131_ = (crate::leanh::lean_unbox(v___x_3130_) as u8);
                    if v___x_3131_ == 0 {
                        v___x_3132_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3133_ = lean_nat_add(v_k_3125_, v___x_3132_);
                        crate::leanh::lean_dec(v_k_3125_);
                        v_k_3125_ = v___x_3133_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3135_ = lean_array_fswap(v_as_3123_, v_i_3124_, v_k_3125_);
                        v___x_3136_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3137_ = lean_nat_add(v_i_3124_, v___x_3136_);
                        crate::leanh::lean_dec(v_i_3124_);
                        v___x_3138_ = lean_nat_add(v_k_3125_, v___x_3136_);
                        crate::leanh::lean_dec(v_k_3125_);
                        v_as_3123_ = v___x_3135_;
                        v_i_3124_ = v___x_3137_;
                        v_k_3125_ = v___x_3138_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___redArg___boxed(
    mut v_lt_3140_: *mut crate::leanh::LeanObject,
    mut v_hi_3141_: *mut crate::leanh::LeanObject,
    mut v_pivot_3142_: *mut crate::leanh::LeanObject,
    mut v_as_3143_: *mut crate::leanh::LeanObject,
    mut v_i_3144_: *mut crate::leanh::LeanObject,
    mut v_k_3145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3146_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___redArg(v_lt_3140_, v_hi_3141_, v_pivot_3142_, v_as_3143_, v_i_3144_, v_k_3145_);
    crate::leanh::lean_dec(v_hi_3141_);
    return v_res_3146_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(
    mut v_lt_3147_: *mut crate::leanh::LeanObject,
    mut v_n_3148_: *mut crate::leanh::LeanObject,
    mut v_as_3149_: *mut crate::leanh::LeanObject,
    mut v_lo_3150_: *mut crate::leanh::LeanObject,
    mut v_hi_3151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: u8 = 0;
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: u8 = 0;
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: u8 = 0;
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: u8 = 0;
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: u8 = 0;
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3163_ = lean_nat_dec_lt(v_lo_3150_, v_hi_3151_);
                if v___x_3163_ == 0 {
                    crate::leanh::lean_dec(v_lo_3150_);
                    crate::leanh::lean_dec_ref(v_lt_3147_);
                    return v_as_3149_;
                } else {
                    v___x_3164_ = lean_nat_add(v_lo_3150_, v_hi_3151_);
                    v___x_3165_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_3166_ = lean_nat_shiftr(v___x_3164_, v___x_3165_);
                    crate::leanh::lean_dec(v___x_3164_);
                    v___x_3181_ = lean_array_fget_borrowed(v_as_3149_, v_mid_3166_);
                    v___x_3182_ = lean_array_fget_borrowed(v_as_3149_, v_lo_3150_);
                    crate::leanh::lean_inc_ref(v_lt_3147_);
                    crate::leanh::lean_inc(v___x_3182_);
                    crate::leanh::lean_inc(v___x_3181_);
                    v___x_3183_ = crate::leanh::lean_apply_2(v_lt_3147_, v___x_3181_, v___x_3182_);
                    v___x_3184_ = (crate::leanh::lean_unbox(v___x_3183_) as u8);
                    if v___x_3184_ == 0 {
                        v___y_3175_ = v_as_3149_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3185_ = lean_array_fswap(v_as_3149_, v_lo_3150_, v_mid_3166_);
                        v___y_3175_ = v___x_3185_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_3154_ = lean_array_fget(v___y_3153_, v_hi_3151_);
                crate::leanh::lean_inc_n(v_lo_3150_, 2);
                crate::leanh::lean_inc_ref(v_lt_3147_);
                v___x_3155_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___redArg(v_lt_3147_, v_hi_3151_, v_pivot_3154_, v___y_3153_, v_lo_3150_, v_lo_3150_);
                v_fst_3156_ = crate::leanh::lean_ctor_get(v___x_3155_, 0);
                crate::leanh::lean_inc(v_fst_3156_);
                v_snd_3157_ = crate::leanh::lean_ctor_get(v___x_3155_, 1);
                crate::leanh::lean_inc(v_snd_3157_);
                crate::leanh::lean_dec_ref(v___x_3155_);
                v___x_3158_ = lean_nat_dec_le(v_hi_3151_, v_fst_3156_);
                if v___x_3158_ == 0 {
                    crate::leanh::lean_inc_ref(v_lt_3147_);
                    v___x_3159_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_3147_, v_n_3148_, v_snd_3157_, v_lo_3150_, v_fst_3156_);
                    v___x_3160_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3161_ = lean_nat_add(v_fst_3156_, v___x_3160_);
                    crate::leanh::lean_dec(v_fst_3156_);
                    v_as_3149_ = v___x_3159_;
                    v_lo_3150_ = v___x_3161_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_3156_);
                    crate::leanh::lean_dec(v_lo_3150_);
                    crate::leanh::lean_dec_ref(v_lt_3147_);
                    return v_snd_3157_;
                }
            }
            2 => {
                v___x_3169_ = lean_array_fget_borrowed(v___y_3168_, v_mid_3166_);
                v___x_3170_ = lean_array_fget_borrowed(v___y_3168_, v_hi_3151_);
                crate::leanh::lean_inc_ref(v_lt_3147_);
                crate::leanh::lean_inc(v___x_3170_);
                crate::leanh::lean_inc(v___x_3169_);
                v___x_3171_ = crate::leanh::lean_apply_2(v_lt_3147_, v___x_3169_, v___x_3170_);
                v___x_3172_ = (crate::leanh::lean_unbox(v___x_3171_) as u8);
                if v___x_3172_ == 0 {
                    crate::leanh::lean_dec(v_mid_3166_);
                    v___y_3153_ = v___y_3168_;
                    state = 1;
                    continue;
                } else {
                    v___x_3173_ = lean_array_fswap(v___y_3168_, v_mid_3166_, v_hi_3151_);
                    crate::leanh::lean_dec(v_mid_3166_);
                    v___y_3153_ = v___x_3173_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3176_ = lean_array_fget_borrowed(v___y_3175_, v_hi_3151_);
                v___x_3177_ = lean_array_fget_borrowed(v___y_3175_, v_lo_3150_);
                crate::leanh::lean_inc_ref(v_lt_3147_);
                crate::leanh::lean_inc(v___x_3177_);
                crate::leanh::lean_inc(v___x_3176_);
                v___x_3178_ = crate::leanh::lean_apply_2(v_lt_3147_, v___x_3176_, v___x_3177_);
                v___x_3179_ = (crate::leanh::lean_unbox(v___x_3178_) as u8);
                if v___x_3179_ == 0 {
                    v___y_3168_ = v___y_3175_;
                    state = 2;
                    continue;
                } else {
                    v___x_3180_ = lean_array_fswap(v___y_3175_, v_lo_3150_, v_hi_3151_);
                    v___y_3168_ = v___x_3180_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg___boxed(
    mut v_lt_3186_: *mut crate::leanh::LeanObject,
    mut v_n_3187_: *mut crate::leanh::LeanObject,
    mut v_as_3188_: *mut crate::leanh::LeanObject,
    mut v_lo_3189_: *mut crate::leanh::LeanObject,
    mut v_hi_3190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3191_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_3186_, v_n_3187_, v_as_3188_, v_lo_3189_, v_hi_3190_);
    crate::leanh::lean_dec(v_hi_3190_);
    crate::leanh::lean_dec(v_n_3187_);
    return v_res_3191_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(
    mut v_s_3195_: *mut crate::leanh::LeanObject,
    mut v_lt_3196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: u8 = 0;
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: u8 = 0;
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3197_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__0;
                v___x_3198_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3199_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__1;
                v_decls_3200_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_s_3195_, v___f_3197_, v___x_3199_);
                v___x_3201_ = lean_array_get_size(v_decls_3200_);
                v___x_3202_ = lean_nat_dec_eq(v___x_3201_, v___x_3198_);
                if v___x_3202_ == 0 {
                    v___x_3203_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3204_ = lean_nat_sub(v___x_3201_, v___x_3203_);
                    v___x_3210_ = lean_nat_dec_le(v___x_3198_, v___x_3204_);
                    if v___x_3210_ == 0 {
                        crate::leanh::lean_inc(v___x_3204_);
                        v___y_3206_ = v___x_3204_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3206_ = v___x_3198_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_lt_3196_);
                    return v_decls_3200_;
                }
            }
            1 => {
                v___x_3207_ = lean_nat_dec_le(v___y_3206_, v___x_3204_);
                if v___x_3207_ == 0 {
                    crate::leanh::lean_dec(v___x_3204_);
                    crate::leanh::lean_inc(v___y_3206_);
                    v___x_3208_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_3196_, v___x_3201_, v_decls_3200_, v___y_3206_, v___y_3206_);
                    crate::leanh::lean_dec(v___y_3206_);
                    return v___x_3208_;
                } else {
                    v___x_3209_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_3196_, v___x_3201_, v_decls_3200_, v___y_3206_, v___x_3204_);
                    crate::leanh::lean_dec(v___x_3204_);
                    return v___x_3209_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___boxed(
    mut v_s_3211_: *mut crate::leanh::LeanObject,
    mut v_lt_3212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3213_ =
        l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(
            v_s_3211_, v_lt_3212_,
        );
    crate::leanh::lean_dec_ref(v_s_3211_);
    return v_res_3213_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries(
    mut v_pu_3214_: u8,
    mut v_00_u03b2_3215_: *mut crate::leanh::LeanObject,
    mut v_s_3216_: *mut crate::leanh::LeanObject,
    mut v_lt_3217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3218_ =
        l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(
            v_s_3216_, v_lt_3217_,
        );
    return v___x_3218_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___boxed(
    mut v_pu_3219_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3220_: *mut crate::leanh::LeanObject,
    mut v_s_3221_: *mut crate::leanh::LeanObject,
    mut v_lt_3222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3223_: u8 = 0;
    let mut v_res_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3223_ = (crate::leanh::lean_unbox(v_pu_3219_) as u8);
    v_res_3224_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries(
        v_pu_boxed_3223_,
        v_00_u03b2_3220_,
        v_s_3221_,
        v_lt_3222_,
    );
    crate::leanh::lean_dec_ref(v_s_3221_);
    return v_res_3224_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0(
    mut v_00_u03c3_3225_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3226_: *mut crate::leanh::LeanObject,
    mut v_map_3227_: *mut crate::leanh::LeanObject,
    mut v_f_3228_: *mut crate::leanh::LeanObject,
    mut v_init_3229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3230_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_map_3227_, v_f_3228_, v_init_3229_);
    return v___x_3230_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___boxed(
    mut v_00_u03c3_3231_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3232_: *mut crate::leanh::LeanObject,
    mut v_map_3233_: *mut crate::leanh::LeanObject,
    mut v_f_3234_: *mut crate::leanh::LeanObject,
    mut v_init_3235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3236_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0(v_00_u03c3_3231_, v_00_u03b2_3232_, v_map_3233_, v_f_3234_, v_init_3235_);
    crate::leanh::lean_dec_ref(v_map_3233_);
    return v_res_3236_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1(
    mut v_00_u03b2_3237_: *mut crate::leanh::LeanObject,
    mut v_lt_3238_: *mut crate::leanh::LeanObject,
    mut v_n_3239_: *mut crate::leanh::LeanObject,
    mut v_as_3240_: *mut crate::leanh::LeanObject,
    mut v_lo_3241_: *mut crate::leanh::LeanObject,
    mut v_hi_3242_: *mut crate::leanh::LeanObject,
    mut v_w_3243_: *mut crate::leanh::LeanObject,
    mut v_hlo_3244_: *mut crate::leanh::LeanObject,
    mut v_hhi_3245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3246_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_3238_, v_n_3239_, v_as_3240_, v_lo_3241_, v_hi_3242_);
    return v___x_3246_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___boxed(
    mut v_00_u03b2_3247_: *mut crate::leanh::LeanObject,
    mut v_lt_3248_: *mut crate::leanh::LeanObject,
    mut v_n_3249_: *mut crate::leanh::LeanObject,
    mut v_as_3250_: *mut crate::leanh::LeanObject,
    mut v_lo_3251_: *mut crate::leanh::LeanObject,
    mut v_hi_3252_: *mut crate::leanh::LeanObject,
    mut v_w_3253_: *mut crate::leanh::LeanObject,
    mut v_hlo_3254_: *mut crate::leanh::LeanObject,
    mut v_hhi_3255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3256_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1(v_00_u03b2_3247_, v_lt_3248_, v_n_3249_, v_as_3250_, v_lo_3251_, v_hi_3252_, v_w_3253_, v_hlo_3254_, v_hhi_3255_);
    crate::leanh::lean_dec(v_hi_3252_);
    crate::leanh::lean_dec(v_n_3249_);
    return v_res_3256_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___redArg(
    mut v_map_3257_: *mut crate::leanh::LeanObject,
    mut v_f_3258_: *mut crate::leanh::LeanObject,
    mut v_init_3259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3260_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_3258_, v_map_3257_, v_init_3259_);
    return v___x_3260_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___redArg___boxed(
    mut v_map_3261_: *mut crate::leanh::LeanObject,
    mut v_f_3262_: *mut crate::leanh::LeanObject,
    mut v_init_3263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3264_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___redArg(v_map_3261_, v_f_3262_, v_init_3263_);
    crate::leanh::lean_dec_ref(v_map_3261_);
    return v_res_3264_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0(
    mut v_00_u03c3_3265_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3266_: *mut crate::leanh::LeanObject,
    mut v_map_3267_: *mut crate::leanh::LeanObject,
    mut v_f_3268_: *mut crate::leanh::LeanObject,
    mut v_init_3269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3270_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_3268_, v_map_3267_, v_init_3269_);
    return v___x_3270_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___boxed(
    mut v_00_u03c3_3271_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3272_: *mut crate::leanh::LeanObject,
    mut v_map_3273_: *mut crate::leanh::LeanObject,
    mut v_f_3274_: *mut crate::leanh::LeanObject,
    mut v_init_3275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3276_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0(v_00_u03c3_3271_, v_00_u03b2_3272_, v_map_3273_, v_f_3274_, v_init_3275_);
    crate::leanh::lean_dec_ref(v_map_3273_);
    return v_res_3276_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2(
    mut v_00_u03b2_3277_: *mut crate::leanh::LeanObject,
    mut v_lt_3278_: *mut crate::leanh::LeanObject,
    mut v_n_3279_: *mut crate::leanh::LeanObject,
    mut v_lo_3280_: *mut crate::leanh::LeanObject,
    mut v_hi_3281_: *mut crate::leanh::LeanObject,
    mut v_hhi_3282_: *mut crate::leanh::LeanObject,
    mut v_pivot_3283_: *mut crate::leanh::LeanObject,
    mut v_as_3284_: *mut crate::leanh::LeanObject,
    mut v_i_3285_: *mut crate::leanh::LeanObject,
    mut v_k_3286_: *mut crate::leanh::LeanObject,
    mut v_ilo_3287_: *mut crate::leanh::LeanObject,
    mut v_ik_3288_: *mut crate::leanh::LeanObject,
    mut v_w_3289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3290_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___redArg(v_lt_3278_, v_hi_3281_, v_pivot_3283_, v_as_3284_, v_i_3285_, v_k_3286_);
    return v___x_3290_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2___boxed(
    mut v_00_u03b2_3291_: *mut crate::leanh::LeanObject,
    mut v_lt_3292_: *mut crate::leanh::LeanObject,
    mut v_n_3293_: *mut crate::leanh::LeanObject,
    mut v_lo_3294_: *mut crate::leanh::LeanObject,
    mut v_hi_3295_: *mut crate::leanh::LeanObject,
    mut v_hhi_3296_: *mut crate::leanh::LeanObject,
    mut v_pivot_3297_: *mut crate::leanh::LeanObject,
    mut v_as_3298_: *mut crate::leanh::LeanObject,
    mut v_i_3299_: *mut crate::leanh::LeanObject,
    mut v_k_3300_: *mut crate::leanh::LeanObject,
    mut v_ilo_3301_: *mut crate::leanh::LeanObject,
    mut v_ik_3302_: *mut crate::leanh::LeanObject,
    mut v_w_3303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3304_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1_spec__2(v_00_u03b2_3291_, v_lt_3292_, v_n_3293_, v_lo_3294_, v_hi_3295_, v_hhi_3296_, v_pivot_3297_, v_as_3298_, v_i_3299_, v_k_3300_, v_ilo_3301_, v_ik_3302_, v_w_3303_);
    crate::leanh::lean_dec(v_hi_3295_);
    crate::leanh::lean_dec(v_lo_3294_);
    crate::leanh::lean_dec(v_n_3293_);
    return v_res_3304_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1(
    mut v_00_u03c3_3305_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3306_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3307_: *mut crate::leanh::LeanObject,
    mut v_f_3308_: *mut crate::leanh::LeanObject,
    mut v_x_3309_: *mut crate::leanh::LeanObject,
    mut v_x_3310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3311_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_3308_, v_x_3309_, v_x_3310_);
    return v___x_3311_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03c3_3312_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3313_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3314_: *mut crate::leanh::LeanObject,
    mut v_f_3315_: *mut crate::leanh::LeanObject,
    mut v_x_3316_: *mut crate::leanh::LeanObject,
    mut v_x_3317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3318_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1(v_00_u03c3_3312_, v_00_u03b1_3313_, v_00_u03b2_3314_, v_f_3315_, v_x_3316_, v_x_3317_);
    crate::leanh::lean_dec_ref(v_x_3316_);
    return v_res_3318_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b1_3319_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3320_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3321_: *mut crate::leanh::LeanObject,
    mut v_f_3322_: *mut crate::leanh::LeanObject,
    mut v_as_3323_: *mut crate::leanh::LeanObject,
    mut v_i_3324_: usize,
    mut v_stop_3325_: usize,
    mut v_b_3326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3322_, v_as_3323_, v_i_3324_, v_stop_3325_, v_b_3326_);
    return v___x_3327_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b1_3328_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3329_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3330_: *mut crate::leanh::LeanObject,
    mut v_f_3331_: *mut crate::leanh::LeanObject,
    mut v_as_3332_: *mut crate::leanh::LeanObject,
    mut v_i_3333_: *mut crate::leanh::LeanObject,
    mut v_stop_3334_: *mut crate::leanh::LeanObject,
    mut v_b_3335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3336_: usize = 0;
    let mut v_stop_boxed_3337_: usize = 0;
    let mut v_res_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3336_ = crate::leanh::lean_unbox_usize(v_i_3333_);
    crate::leanh::lean_dec(v_i_3333_);
    v_stop_boxed_3337_ = crate::leanh::lean_unbox_usize(v_stop_3334_);
    crate::leanh::lean_dec(v_stop_3334_);
    v_res_3338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_3328_, v_00_u03b2_3329_, v_00_u03c3_3330_, v_f_3331_, v_as_3332_, v_i_boxed_3336_, v_stop_boxed_3337_, v_b_3335_);
    crate::leanh::lean_dec_ref(v_as_3332_);
    return v_res_3338_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03c3_3339_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3340_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3341_: *mut crate::leanh::LeanObject,
    mut v_f_3342_: *mut crate::leanh::LeanObject,
    mut v_keys_3343_: *mut crate::leanh::LeanObject,
    mut v_vals_3344_: *mut crate::leanh::LeanObject,
    mut v_heq_3345_: *mut crate::leanh::LeanObject,
    mut v_i_3346_: *mut crate::leanh::LeanObject,
    mut v_acc_3347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3348_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg(v_f_3342_, v_keys_3343_, v_vals_3344_, v_i_3346_, v_acc_3347_);
    return v___x_3348_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03c3_3349_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3350_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3351_: *mut crate::leanh::LeanObject,
    mut v_f_3352_: *mut crate::leanh::LeanObject,
    mut v_keys_3353_: *mut crate::leanh::LeanObject,
    mut v_vals_3354_: *mut crate::leanh::LeanObject,
    mut v_heq_3355_: *mut crate::leanh::LeanObject,
    mut v_i_3356_: *mut crate::leanh::LeanObject,
    mut v_acc_3357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3358_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4(v_00_u03c3_3349_, v_00_u03b1_3350_, v_00_u03b2_3351_, v_f_3352_, v_keys_3353_, v_vals_3354_, v_heq_3355_, v_i_3356_, v_acc_3357_);
    crate::leanh::lean_dec_ref(v_vals_3354_);
    crate::leanh::lean_dec_ref(v_keys_3353_);
    return v_res_3358_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(
    mut v_keys_3359_: *mut crate::leanh::LeanObject,
    mut v_i_3360_: *mut crate::leanh::LeanObject,
    mut v_k_3361_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: u8 = 0;
    let mut v_k_x27_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: u8 = 0;
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3362_ = lean_array_get_size(v_keys_3359_);
                v___x_3363_ = lean_nat_dec_lt(v_i_3360_, v___x_3362_);
                if v___x_3363_ == 0 {
                    crate::leanh::lean_dec(v_i_3360_);
                    return v___x_3363_;
                } else {
                    v_k_x27_3364_ = lean_array_fget_borrowed(v_keys_3359_, v_i_3360_);
                    v___x_3365_ = lean_name_eq(v_k_3361_, v_k_x27_3364_);
                    if v___x_3365_ == 0 {
                        v___x_3366_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3367_ = lean_nat_add(v_i_3360_, v___x_3366_);
                        crate::leanh::lean_dec(v_i_3360_);
                        v_i_3360_ = v___x_3367_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_3360_);
                        return v___x_3365_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_3369_: *mut crate::leanh::LeanObject,
    mut v_i_3370_: *mut crate::leanh::LeanObject,
    mut v_k_3371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3372_: u8 = 0;
    let mut v_r_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3372_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(v_keys_3369_, v_i_3370_, v_k_3371_);
    crate::leanh::lean_dec(v_k_3371_);
    crate::leanh::lean_dec_ref(v_keys_3369_);
    v_r_3373_ = crate::leanh::lean_box((v_res_3372_) as usize);
    return v_r_3373_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_3374_: usize = 0;
    let mut v___x_3375_: usize = 0;
    let mut v___x_3376_: usize = 0;
    v___x_3374_ = 5usize;
    v___x_3375_ = 1usize;
    v___x_3376_ = lean_usize_shift_left(v___x_3375_, v___x_3374_);
    return v___x_3376_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_3377_: usize = 0;
    let mut v___x_3378_: usize = 0;
    let mut v___x_3379_: usize = 0;
    v___x_3377_ = 1usize;
    v___x_3378_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__0);
    v___x_3379_ = lean_usize_sub(v___x_3378_, v___x_3377_);
    return v___x_3379_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(
    mut v_x_3380_: *mut crate::leanh::LeanObject,
    mut v_x_3381_: usize,
    mut v_x_3382_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: usize = 0;
    let mut v___x_3386_: usize = 0;
    let mut v___x_3387_: usize = 0;
    let mut v_j_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: u8 = 0;
    let mut v_node_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: usize = 0;
    let mut v___x_3395_: u8 = 0;
    let mut v_ks_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3380_) == 0 {
                    v_es_3383_ = crate::leanh::lean_ctor_get(v_x_3380_, 0);
                    v___x_3384_ = crate::leanh::lean_box(2);
                    v___x_3385_ = 5usize;
                    v___x_3386_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1);
                    v___x_3387_ = lean_usize_land(v_x_3381_, v___x_3386_);
                    v_j_3388_ = lean_usize_to_nat(v___x_3387_);
                    v___x_3389_ = lean_array_get_borrowed(v___x_3384_, v_es_3383_, v_j_3388_);
                    crate::leanh::lean_dec(v_j_3388_);
                    match crate::leanh::lean_obj_tag(v___x_3389_) {
                        0 => {
                            v_key_3390_ = crate::leanh::lean_ctor_get(v___x_3389_, 0);
                            v___x_3391_ = lean_name_eq(v_x_3382_, v_key_3390_);
                            return v___x_3391_;
                        }
                        1 => {
                            v_node_3392_ = crate::leanh::lean_ctor_get(v___x_3389_, 0);
                            v___x_3393_ = lean_usize_shift_right(v_x_3381_, v___x_3385_);
                            v_x_3380_ = v_node_3392_;
                            v_x_3381_ = v___x_3393_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3395_ = 0;
                            return v___x_3395_;
                        }
                    }
                } else {
                    v_ks_3396_ = crate::leanh::lean_ctor_get(v_x_3380_, 0);
                    v___x_3397_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3398_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(v_ks_3396_, v___x_3397_, v_x_3382_);
                    return v___x_3398_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___boxed(
    mut v_x_3399_: *mut crate::leanh::LeanObject,
    mut v_x_3400_: *mut crate::leanh::LeanObject,
    mut v_x_3401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_433__boxed_3402_: usize = 0;
    let mut v_res_3403_: u8 = 0;
    let mut v_r_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_433__boxed_3402_ = crate::leanh::lean_unbox_usize(v_x_3400_);
    crate::leanh::lean_dec(v_x_3400_);
    v_res_3403_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(v_x_3399_, v_x_433__boxed_3402_, v_x_3401_);
    crate::leanh::lean_dec(v_x_3401_);
    crate::leanh::lean_dec_ref(v_x_3399_);
    v_r_3404_ = crate::leanh::lean_box((v_res_3403_) as usize);
    return v_r_3404_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0()
-> u64 {
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: u64 = 0;
    v___x_3405_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_3406_ = lean_uint64_of_nat(v___x_3405_);
    return v___x_3406_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(
    mut v_x_3407_: *mut crate::leanh::LeanObject,
    mut v_x_3408_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_3410_: u64 = 0;
    let mut v___x_3411_: usize = 0;
    let mut v___x_3412_: u8 = 0;
    let mut v___x_3413_: u64 = 0;
    let mut v_hash_3414_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3408_) == 0 {
                    v___x_3413_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
                    v___y_3410_ = v___x_3413_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3414_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_3408_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3410_ = v_hash_3414_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3411_ = lean_uint64_to_usize(v___y_3410_);
                v___x_3412_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(v_x_3407_, v___x_3411_, v_x_3408_);
                return v___x_3412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___boxed(
    mut v_x_3415_: *mut crate::leanh::LeanObject,
    mut v_x_3416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3417_: u8 = 0;
    let mut v_r_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3417_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(v_x_3415_, v_x_3416_);
    crate::leanh::lean_dec(v_x_3416_);
    crate::leanh::lean_dec_ref(v_x_3415_);
    v_r_3418_ = crate::leanh::lean_box((v_res_3417_) as usize);
    return v_r_3418_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_x_3419_: *mut crate::leanh::LeanObject,
    mut v_x_3420_: *mut crate::leanh::LeanObject,
    mut v_x_3421_: *mut crate::leanh::LeanObject,
    mut v_x_3422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3427_: u8 = 0;
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: u8 = 0;
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: u8 = 0;
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3448_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3423_ = crate::leanh::lean_ctor_get(v_x_3419_, 0);
                v_vs_3424_ = crate::leanh::lean_ctor_get(v_x_3419_, 1);
                v_isSharedCheck_3448_ = (!crate::leanh::lean_is_exclusive(v_x_3419_)) as u8;
                if v_isSharedCheck_3448_ == 0 {
                    v___x_3426_ = v_x_3419_;
                    v_isShared_3427_ = v_isSharedCheck_3448_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_3424_);
                    crate::leanh::lean_inc(v_ks_3423_);
                    crate::leanh::lean_dec(v_x_3419_);
                    v___x_3426_ = crate::leanh::lean_box(0);
                    v_isShared_3427_ = v_isSharedCheck_3448_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3428_ = lean_array_get_size(v_ks_3423_);
                v___x_3429_ = lean_nat_dec_lt(v_x_3420_, v___x_3428_);
                if v___x_3429_ == 0 {
                    crate::leanh::lean_dec(v_x_3420_);
                    v___x_3430_ = lean_array_push(v_ks_3423_, v_x_3421_);
                    v___x_3431_ = lean_array_push(v_vs_3424_, v_x_3422_);
                    if v_isShared_3427_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3426_, 1, v___x_3431_);
                        crate::leanh::lean_ctor_set(v___x_3426_, 0, v___x_3430_);
                        v___x_3433_ = v___x_3426_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3434_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3430_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3434_, 1, v___x_3431_);
                        v___x_3433_ = v_reuseFailAlloc_3434_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3435_ = lean_array_fget_borrowed(v_ks_3423_, v_x_3420_);
                    v___x_3436_ = lean_name_eq(v_x_3421_, v_k_x27_3435_);
                    if v___x_3436_ == 0 {
                        if v_isShared_3427_ == 0 {
                            v___x_3438_ = v___x_3426_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3442_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_ks_3423_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3442_, 1, v_vs_3424_);
                            v___x_3438_ = v_reuseFailAlloc_3442_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3443_ = lean_array_fset(v_ks_3423_, v_x_3420_, v_x_3421_);
                        v___x_3444_ = lean_array_fset(v_vs_3424_, v_x_3420_, v_x_3422_);
                        crate::leanh::lean_dec(v_x_3420_);
                        if v_isShared_3427_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3426_, 1, v___x_3444_);
                            crate::leanh::lean_ctor_set(v___x_3426_, 0, v___x_3443_);
                            v___x_3446_ = v___x_3426_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3447_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3443_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3447_, 1, v___x_3444_);
                            v___x_3446_ = v_reuseFailAlloc_3447_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3433_;
            }
            3 => {
                v___x_3439_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3440_ = lean_nat_add(v_x_3420_, v___x_3439_);
                crate::leanh::lean_dec(v_x_3420_);
                v_x_3419_ = v___x_3438_;
                v_x_3420_ = v___x_3440_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3446_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4___redArg(
    mut v_n_3449_: *mut crate::leanh::LeanObject,
    mut v_k_3450_: *mut crate::leanh::LeanObject,
    mut v_v_3451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3452_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3453_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5___redArg(v_n_3449_, v___x_3452_, v_k_3450_, v_v_3451_);
    return v___x_3453_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3454_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3454_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(
    mut v_x_3455_: *mut crate::leanh::LeanObject,
    mut v_x_3456_: usize,
    mut v_x_3457_: usize,
    mut v_x_3458_: *mut crate::leanh::LeanObject,
    mut v_x_3459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: usize = 0;
    let mut v___x_3462_: usize = 0;
    let mut v___x_3463_: usize = 0;
    let mut v___x_3464_: usize = 0;
    let mut v_j_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: u8 = 0;
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3470_: u8 = 0;
    let mut v_v_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3484_: u8 = 0;
    let mut v___x_3485_: u8 = 0;
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3491_: u8 = 0;
    let mut v_node_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3495_: u8 = 0;
    let mut v___x_3496_: usize = 0;
    let mut v___x_3497_: usize = 0;
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3502_: u8 = 0;
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3504_: u8 = 0;
    let mut v_unused_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3510_: u8 = 0;
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3515_: u8 = 0;
    let mut v_ks_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: usize = 0;
    let mut v___x_3522_: u8 = 0;
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: u8 = 0;
    let mut v_reuseFailAlloc_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3455_) == 0 {
                    v_es_3460_ = crate::leanh::lean_ctor_get(v_x_3455_, 0);
                    v___x_3461_ = 5usize;
                    v___x_3462_ = 1usize;
                    v___x_3463_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1);
                    v___x_3464_ = lean_usize_land(v_x_3456_, v___x_3463_);
                    v_j_3465_ = lean_usize_to_nat(v___x_3464_);
                    v___x_3466_ = lean_array_get_size(v_es_3460_);
                    v___x_3467_ = lean_nat_dec_lt(v_j_3465_, v___x_3466_);
                    if v___x_3467_ == 0 {
                        crate::leanh::lean_dec(v_j_3465_);
                        crate::leanh::lean_dec(v_x_3459_);
                        crate::leanh::lean_dec(v_x_3458_);
                        return v_x_3455_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_3460_);
                        v_isSharedCheck_3504_ = (!crate::leanh::lean_is_exclusive(v_x_3455_)) as u8;
                        if v_isSharedCheck_3504_ == 0 {
                            v_unused_3505_ = crate::leanh::lean_ctor_get(v_x_3455_, 0);
                            crate::leanh::lean_dec(v_unused_3505_);
                            v___x_3469_ = v_x_3455_;
                            v_isShared_3470_ = v_isSharedCheck_3504_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_3455_);
                            v___x_3469_ = crate::leanh::lean_box(0);
                            v_isShared_3470_ = v_isSharedCheck_3504_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3506_ = crate::leanh::lean_ctor_get(v_x_3455_, 0);
                    v_vs_3507_ = crate::leanh::lean_ctor_get(v_x_3455_, 1);
                    v_isSharedCheck_3527_ = (!crate::leanh::lean_is_exclusive(v_x_3455_)) as u8;
                    if v_isSharedCheck_3527_ == 0 {
                        v___x_3509_ = v_x_3455_;
                        v_isShared_3510_ = v_isSharedCheck_3527_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_3507_);
                        crate::leanh::lean_inc(v_ks_3506_);
                        crate::leanh::lean_dec(v_x_3455_);
                        v___x_3509_ = crate::leanh::lean_box(0);
                        v_isShared_3510_ = v_isSharedCheck_3527_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3471_ = lean_array_fget(v_es_3460_, v_j_3465_);
                v___x_3472_ = crate::leanh::lean_box(0);
                v_xs_x27_3473_ = lean_array_fset(v_es_3460_, v_j_3465_, v___x_3472_);
                match crate::leanh::lean_obj_tag(v_v_3471_) {
                    0 => {
                        v_key_3480_ = crate::leanh::lean_ctor_get(v_v_3471_, 0);
                        v_val_3481_ = crate::leanh::lean_ctor_get(v_v_3471_, 1);
                        v_isSharedCheck_3491_ = (!crate::leanh::lean_is_exclusive(v_v_3471_)) as u8;
                        if v_isSharedCheck_3491_ == 0 {
                            v___x_3483_ = v_v_3471_;
                            v_isShared_3484_ = v_isSharedCheck_3491_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3481_);
                            crate::leanh::lean_inc(v_key_3480_);
                            crate::leanh::lean_dec(v_v_3471_);
                            v___x_3483_ = crate::leanh::lean_box(0);
                            v_isShared_3484_ = v_isSharedCheck_3491_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3492_ = crate::leanh::lean_ctor_get(v_v_3471_, 0);
                        v_isSharedCheck_3502_ = (!crate::leanh::lean_is_exclusive(v_v_3471_)) as u8;
                        if v_isSharedCheck_3502_ == 0 {
                            v___x_3494_ = v_v_3471_;
                            v_isShared_3495_ = v_isSharedCheck_3502_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_3492_);
                            crate::leanh::lean_dec(v_v_3471_);
                            v___x_3494_ = crate::leanh::lean_box(0);
                            v_isShared_3495_ = v_isSharedCheck_3502_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3503_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3503_, 0, v_x_3458_);
                        crate::leanh::lean_ctor_set(v___x_3503_, 1, v_x_3459_);
                        v___y_3475_ = v___x_3503_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3476_ = lean_array_fset(v_xs_x27_3473_, v_j_3465_, v___y_3475_);
                crate::leanh::lean_dec(v_j_3465_);
                if v_isShared_3470_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3469_, 0, v___x_3476_);
                    v___x_3478_ = v___x_3469_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3479_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3476_);
                    v___x_3478_ = v_reuseFailAlloc_3479_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3478_;
            }
            4 => {
                v___x_3485_ = lean_name_eq(v_x_3458_, v_key_3480_);
                if v___x_3485_ == 0 {
                    crate::leanh::lean_del_object(v___x_3483_);
                    v___x_3486_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3480_,
                        v_val_3481_,
                        v_x_3458_,
                        v_x_3459_,
                    );
                    v___x_3487_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3487_, 0, v___x_3486_);
                    v___y_3475_ = v___x_3487_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_3481_);
                    crate::leanh::lean_dec(v_key_3480_);
                    if v_isShared_3484_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3483_, 1, v_x_3459_);
                        crate::leanh::lean_ctor_set(v___x_3483_, 0, v_x_3458_);
                        v___x_3489_ = v___x_3483_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3490_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_x_3458_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3490_, 1, v_x_3459_);
                        v___x_3489_ = v_reuseFailAlloc_3490_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3475_ = v___x_3489_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3496_ = lean_usize_shift_right(v_x_3456_, v___x_3461_);
                v___x_3497_ = lean_usize_add(v_x_3457_, v___x_3462_);
                v___x_3498_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_node_3492_, v___x_3496_, v___x_3497_, v_x_3458_, v_x_3459_);
                if v_isShared_3495_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3494_, 0, v___x_3498_);
                    v___x_3500_ = v___x_3494_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3501_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3498_);
                    v___x_3500_ = v_reuseFailAlloc_3501_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3475_ = v___x_3500_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3510_ == 0 {
                    v___x_3512_ = v___x_3509_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3526_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_ks_3506_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3526_, 1, v_vs_3507_);
                    v___x_3512_ = v_reuseFailAlloc_3526_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3513_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4___redArg(v___x_3512_, v_x_3458_, v_x_3459_);
                v___x_3521_ = 7usize;
                v___x_3522_ = lean_usize_dec_le(v___x_3521_, v_x_3457_);
                if v___x_3522_ == 0 {
                    v___x_3523_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3513_);
                    v___x_3524_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3525_ = lean_nat_dec_lt(v___x_3523_, v___x_3524_);
                    crate::leanh::lean_dec(v___x_3523_);
                    v___y_3515_ = v___x_3525_;
                    state = 10;
                    continue;
                } else {
                    v___y_3515_ = v___x_3522_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3515_ == 0 {
                    v_ks_3516_ = crate::leanh::lean_ctor_get(v_newNode_3513_, 0);
                    crate::leanh::lean_inc_ref(v_ks_3516_);
                    v_vs_3517_ = crate::leanh::lean_ctor_get(v_newNode_3513_, 1);
                    crate::leanh::lean_inc_ref(v_vs_3517_);
                    crate::leanh::lean_dec_ref(v_newNode_3513_);
                    v___x_3518_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3519_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0);
                    v___x_3520_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(v_x_3457_, v_ks_3516_, v_vs_3517_, v___x_3518_, v___x_3519_);
                    crate::leanh::lean_dec_ref(v_vs_3517_);
                    crate::leanh::lean_dec_ref(v_ks_3516_);
                    return v___x_3520_;
                } else {
                    return v_newNode_3513_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(
    mut v_depth_3528_: usize,
    mut v_keys_3529_: *mut crate::leanh::LeanObject,
    mut v_vals_3530_: *mut crate::leanh::LeanObject,
    mut v_i_3531_: *mut crate::leanh::LeanObject,
    mut v_entries_3532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: u8 = 0;
    let mut v_k_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3538_: u64 = 0;
    let mut v_h_3539_: usize = 0;
    let mut v___x_3540_: usize = 0;
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: usize = 0;
    let mut v___x_3543_: usize = 0;
    let mut v___x_3544_: usize = 0;
    let mut v_h_3545_: usize = 0;
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: u64 = 0;
    let mut v_hash_3550_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3533_ = lean_array_get_size(v_keys_3529_);
                v___x_3534_ = lean_nat_dec_lt(v_i_3531_, v___x_3533_);
                if v___x_3534_ == 0 {
                    crate::leanh::lean_dec(v_i_3531_);
                    return v_entries_3532_;
                } else {
                    v_k_3535_ = lean_array_fget_borrowed(v_keys_3529_, v_i_3531_);
                    v_v_3536_ = lean_array_fget_borrowed(v_vals_3530_, v_i_3531_);
                    if crate::leanh::lean_obj_tag(v_k_3535_) == 0 {
                        v___x_3549_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
                        v___y_3538_ = v___x_3549_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_3550_ = crate::leanh::lean_ctor_get_uint64(
                            v_k_3535_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_3538_ = v_hash_3550_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_3539_ = lean_uint64_to_usize(v___y_3538_);
                v___x_3540_ = 5usize;
                v___x_3541_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3542_ = 1usize;
                v___x_3543_ = lean_usize_sub(v_depth_3528_, v___x_3542_);
                v___x_3544_ = lean_usize_mul(v___x_3540_, v___x_3543_);
                v_h_3545_ = lean_usize_shift_right(v_h_3539_, v___x_3544_);
                v___x_3546_ = lean_nat_add(v_i_3531_, v___x_3541_);
                crate::leanh::lean_dec(v_i_3531_);
                crate::leanh::lean_inc(v_v_3536_);
                crate::leanh::lean_inc(v_k_3535_);
                v___x_3547_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_entries_3532_, v_h_3545_, v_depth_3528_, v_k_3535_, v_v_3536_);
                v_i_3531_ = v___x_3546_;
                v_entries_3532_ = v___x_3547_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_depth_3551_: *mut crate::leanh::LeanObject,
    mut v_keys_3552_: *mut crate::leanh::LeanObject,
    mut v_vals_3553_: *mut crate::leanh::LeanObject,
    mut v_i_3554_: *mut crate::leanh::LeanObject,
    mut v_entries_3555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3556_: usize = 0;
    let mut v_res_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3556_ = crate::leanh::lean_unbox_usize(v_depth_3551_);
    crate::leanh::lean_dec(v_depth_3551_);
    v_res_3557_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(v_depth_boxed_3556_, v_keys_3552_, v_vals_3553_, v_i_3554_, v_entries_3555_);
    crate::leanh::lean_dec_ref(v_vals_3553_);
    crate::leanh::lean_dec_ref(v_keys_3552_);
    return v_res_3557_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___boxed(
    mut v_x_3558_: *mut crate::leanh::LeanObject,
    mut v_x_3559_: *mut crate::leanh::LeanObject,
    mut v_x_3560_: *mut crate::leanh::LeanObject,
    mut v_x_3561_: *mut crate::leanh::LeanObject,
    mut v_x_3562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_589__boxed_3563_: usize = 0;
    let mut v_x_590__boxed_3564_: usize = 0;
    let mut v_res_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_589__boxed_3563_ = crate::leanh::lean_unbox_usize(v_x_3559_);
    crate::leanh::lean_dec(v_x_3559_);
    v_x_590__boxed_3564_ = crate::leanh::lean_unbox_usize(v_x_3560_);
    crate::leanh::lean_dec(v_x_3560_);
    v_res_3565_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_x_3558_, v_x_589__boxed_3563_, v_x_590__boxed_3564_, v_x_3561_, v_x_3562_);
    return v_res_3565_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(
    mut v_x_3566_: *mut crate::leanh::LeanObject,
    mut v_x_3567_: *mut crate::leanh::LeanObject,
    mut v_x_3568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3570_: u64 = 0;
    let mut v___x_3571_: usize = 0;
    let mut v___x_3572_: usize = 0;
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: u64 = 0;
    let mut v_hash_3575_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3567_) == 0 {
                    v___x_3574_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
                    v___y_3570_ = v___x_3574_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3575_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_3567_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3570_ = v_hash_3575_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3571_ = lean_uint64_to_usize(v___y_3570_);
                v___x_3572_ = 1usize;
                v___x_3573_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_x_3566_, v___x_3571_, v___x_3572_, v_x_3567_, v_x_3568_);
                return v___x_3573_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___lam__0(
    mut v_oldState_3576_: *mut crate::leanh::LeanObject,
    mut v_otherState_3577_: *mut crate::leanh::LeanObject,
    mut v_k_3578_: *mut crate::leanh::LeanObject,
    mut v_v_3579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3580_: u8 = 0;
    v___x_3580_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(v_oldState_3576_, v_k_3578_);
    if v___x_3580_ == 0 {
        let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3581_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_otherState_3577_, v_k_3578_, v_v_3579_);
        return v___x_3581_;
    } else {
        crate::leanh::lean_dec(v_v_3579_);
        crate::leanh::lean_dec(v_k_3578_);
        return v_otherState_3577_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___lam__0___boxed(
    mut v_oldState_3582_: *mut crate::leanh::LeanObject,
    mut v_otherState_3583_: *mut crate::leanh::LeanObject,
    mut v_k_3584_: *mut crate::leanh::LeanObject,
    mut v_v_3585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3586_ =
        l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___lam__0(
            v_oldState_3582_,
            v_otherState_3583_,
            v_k_3584_,
            v_v_3585_,
        );
    crate::leanh::lean_dec_ref(v_oldState_3582_);
    return v_res_3586_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg(
    mut v_oldState_3587_: *mut crate::leanh::LeanObject,
    mut v_newState_3588_: *mut crate::leanh::LeanObject,
    mut v_otherState_3589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3590_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
    crate::leanh::lean_closure_set(v___f_3590_, 0, v_oldState_3587_);
    v___x_3591_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_newState_3588_, v___f_3590_, v_otherState_3589_);
    return v___x_3591_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___boxed(
    mut v_oldState_3592_: *mut crate::leanh::LeanObject,
    mut v_newState_3593_: *mut crate::leanh::LeanObject,
    mut v_otherState_3594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3595_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg(
        v_oldState_3592_,
        v_newState_3593_,
        v_otherState_3594_,
    );
    crate::leanh::lean_dec_ref(v_newState_3593_);
    return v_res_3595_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn(
    mut v_00_u03b2_3596_: *mut crate::leanh::LeanObject,
    mut v_phase_3597_: u8,
    mut v_oldState_3598_: *mut crate::leanh::LeanObject,
    mut v_newState_3599_: *mut crate::leanh::LeanObject,
    mut v_x_3600_: *mut crate::leanh::LeanObject,
    mut v_otherState_3601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3602_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg(
        v_oldState_3598_,
        v_newState_3599_,
        v_otherState_3601_,
    );
    return v___x_3602_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed(
    mut v_00_u03b2_3603_: *mut crate::leanh::LeanObject,
    mut v_phase_3604_: *mut crate::leanh::LeanObject,
    mut v_oldState_3605_: *mut crate::leanh::LeanObject,
    mut v_newState_3606_: *mut crate::leanh::LeanObject,
    mut v_x_3607_: *mut crate::leanh::LeanObject,
    mut v_otherState_3608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_3609_: u8 = 0;
    let mut v_res_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_3609_ = (crate::leanh::lean_unbox(v_phase_3604_) as u8);
    v_res_3610_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn(
        v_00_u03b2_3603_,
        v_phase_boxed_3609_,
        v_oldState_3605_,
        v_newState_3606_,
        v_x_3607_,
        v_otherState_3608_,
    );
    crate::leanh::lean_dec(v_x_3607_);
    crate::leanh::lean_dec_ref(v_newState_3606_);
    return v_res_3610_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0(
    mut v_00_u03b2_3611_: *mut crate::leanh::LeanObject,
    mut v_x_3612_: *mut crate::leanh::LeanObject,
    mut v_x_3613_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3614_: u8 = 0;
    v___x_3614_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(v_x_3612_, v_x_3613_);
    return v___x_3614_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___boxed(
    mut v_00_u03b2_3615_: *mut crate::leanh::LeanObject,
    mut v_x_3616_: *mut crate::leanh::LeanObject,
    mut v_x_3617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3618_: u8 = 0;
    let mut v_r_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3618_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0(v_00_u03b2_3615_, v_x_3616_, v_x_3617_);
    crate::leanh::lean_dec(v_x_3617_);
    crate::leanh::lean_dec_ref(v_x_3616_);
    v_r_3619_ = crate::leanh::lean_box((v_res_3618_) as usize);
    return v_r_3619_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1(
    mut v_00_u03b2_3620_: *mut crate::leanh::LeanObject,
    mut v_x_3621_: *mut crate::leanh::LeanObject,
    mut v_x_3622_: *mut crate::leanh::LeanObject,
    mut v_x_3623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3624_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_x_3621_, v_x_3622_, v_x_3623_);
    return v___x_3624_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0(
    mut v_00_u03b2_3625_: *mut crate::leanh::LeanObject,
    mut v_x_3626_: *mut crate::leanh::LeanObject,
    mut v_x_3627_: usize,
    mut v_x_3628_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3629_: u8 = 0;
    v___x_3629_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(v_x_3626_, v_x_3627_, v_x_3628_);
    return v___x_3629_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___boxed(
    mut v_00_u03b2_3630_: *mut crate::leanh::LeanObject,
    mut v_x_3631_: *mut crate::leanh::LeanObject,
    mut v_x_3632_: *mut crate::leanh::LeanObject,
    mut v_x_3633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_797__boxed_3634_: usize = 0;
    let mut v_res_3635_: u8 = 0;
    let mut v_r_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_797__boxed_3634_ = crate::leanh::lean_unbox_usize(v_x_3632_);
    crate::leanh::lean_dec(v_x_3632_);
    v_res_3635_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0(v_00_u03b2_3630_, v_x_3631_, v_x_797__boxed_3634_, v_x_3633_);
    crate::leanh::lean_dec(v_x_3633_);
    crate::leanh::lean_dec_ref(v_x_3631_);
    v_r_3636_ = crate::leanh::lean_box((v_res_3635_) as usize);
    return v_r_3636_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2(
    mut v_00_u03b2_3637_: *mut crate::leanh::LeanObject,
    mut v_x_3638_: *mut crate::leanh::LeanObject,
    mut v_x_3639_: usize,
    mut v_x_3640_: usize,
    mut v_x_3641_: *mut crate::leanh::LeanObject,
    mut v_x_3642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3643_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_x_3638_, v_x_3639_, v_x_3640_, v_x_3641_, v_x_3642_);
    return v___x_3643_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___boxed(
    mut v_00_u03b2_3644_: *mut crate::leanh::LeanObject,
    mut v_x_3645_: *mut crate::leanh::LeanObject,
    mut v_x_3646_: *mut crate::leanh::LeanObject,
    mut v_x_3647_: *mut crate::leanh::LeanObject,
    mut v_x_3648_: *mut crate::leanh::LeanObject,
    mut v_x_3649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_808__boxed_3650_: usize = 0;
    let mut v_x_809__boxed_3651_: usize = 0;
    let mut v_res_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_808__boxed_3650_ = crate::leanh::lean_unbox_usize(v_x_3646_);
    crate::leanh::lean_dec(v_x_3646_);
    v_x_809__boxed_3651_ = crate::leanh::lean_unbox_usize(v_x_3647_);
    crate::leanh::lean_dec(v_x_3647_);
    v_res_3652_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2(v_00_u03b2_3644_, v_x_3645_, v_x_808__boxed_3650_, v_x_809__boxed_3651_, v_x_3648_, v_x_3649_);
    return v_res_3652_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3653_: *mut crate::leanh::LeanObject,
    mut v_keys_3654_: *mut crate::leanh::LeanObject,
    mut v_vals_3655_: *mut crate::leanh::LeanObject,
    mut v_heq_3656_: *mut crate::leanh::LeanObject,
    mut v_i_3657_: *mut crate::leanh::LeanObject,
    mut v_k_3658_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3659_: u8 = 0;
    v___x_3659_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(v_keys_3654_, v_i_3657_, v_k_3658_);
    return v___x_3659_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3660_: *mut crate::leanh::LeanObject,
    mut v_keys_3661_: *mut crate::leanh::LeanObject,
    mut v_vals_3662_: *mut crate::leanh::LeanObject,
    mut v_heq_3663_: *mut crate::leanh::LeanObject,
    mut v_i_3664_: *mut crate::leanh::LeanObject,
    mut v_k_3665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3666_: u8 = 0;
    let mut v_r_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3666_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1(v_00_u03b2_3660_, v_keys_3661_, v_vals_3662_, v_heq_3663_, v_i_3664_, v_k_3665_);
    crate::leanh::lean_dec(v_k_3665_);
    crate::leanh::lean_dec_ref(v_vals_3662_);
    crate::leanh::lean_dec_ref(v_keys_3661_);
    v_r_3667_ = crate::leanh::lean_box((v_res_3666_) as usize);
    return v_r_3667_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4(
    mut v_00_u03b2_3668_: *mut crate::leanh::LeanObject,
    mut v_n_3669_: *mut crate::leanh::LeanObject,
    mut v_k_3670_: *mut crate::leanh::LeanObject,
    mut v_v_3671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3672_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4___redArg(v_n_3669_, v_k_3670_, v_v_3671_);
    return v___x_3672_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5(
    mut v_00_u03b2_3673_: *mut crate::leanh::LeanObject,
    mut v_depth_3674_: usize,
    mut v_keys_3675_: *mut crate::leanh::LeanObject,
    mut v_vals_3676_: *mut crate::leanh::LeanObject,
    mut v_heq_3677_: *mut crate::leanh::LeanObject,
    mut v_i_3678_: *mut crate::leanh::LeanObject,
    mut v_entries_3679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3680_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(v_depth_3674_, v_keys_3675_, v_vals_3676_, v_i_3678_, v_entries_3679_);
    return v___x_3680_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_3681_: *mut crate::leanh::LeanObject,
    mut v_depth_3682_: *mut crate::leanh::LeanObject,
    mut v_keys_3683_: *mut crate::leanh::LeanObject,
    mut v_vals_3684_: *mut crate::leanh::LeanObject,
    mut v_heq_3685_: *mut crate::leanh::LeanObject,
    mut v_i_3686_: *mut crate::leanh::LeanObject,
    mut v_entries_3687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3688_: usize = 0;
    let mut v_res_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3688_ = crate::leanh::lean_unbox_usize(v_depth_3682_);
    crate::leanh::lean_dec(v_depth_3682_);
    v_res_3689_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5(v_00_u03b2_3681_, v_depth_boxed_3688_, v_keys_3683_, v_vals_3684_, v_heq_3685_, v_i_3686_, v_entries_3687_);
    crate::leanh::lean_dec_ref(v_vals_3684_);
    crate::leanh::lean_dec_ref(v_keys_3683_);
    return v_res_3689_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5(
    mut v_00_u03b2_3690_: *mut crate::leanh::LeanObject,
    mut v_x_3691_: *mut crate::leanh::LeanObject,
    mut v_x_3692_: *mut crate::leanh::LeanObject,
    mut v_x_3693_: *mut crate::leanh::LeanObject,
    mut v_x_3694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3695_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5___redArg(v_x_3691_, v_x_3692_, v_x_3693_, v_x_3694_);
    return v___x_3695_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0(
    mut v_count_3696_: *mut crate::leanh::LeanObject,
    mut v_x_3697_: *mut crate::leanh::LeanObject,
    mut v_x_3698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3699_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3700_ = lean_nat_add(v_count_3696_, v___x_3699_);
    return v___x_3700_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0___boxed(
    mut v_count_3701_: *mut crate::leanh::LeanObject,
    mut v_x_3702_: *mut crate::leanh::LeanObject,
    mut v_x_3703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3704_ =
        l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0(
            v_count_3701_,
            v_x_3702_,
            v_x_3703_,
        );
    crate::leanh::lean_dec(v_x_3703_);
    crate::leanh::lean_dec(v_x_3702_);
    crate::leanh::lean_dec(v_count_3701_);
    return v_res_3704_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg(
    mut v_state_3709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEntries_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3710_ =
        l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__0;
    v___x_3711_ = crate::leanh::lean_unsigned_to_nat(0);
    v_numEntries_3712_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_state_3709_, v___f_3710_, v___x_3711_);
    v___x_3713_ =
        l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__2;
    v___x_3714_ = l_Nat_reprFast(v_numEntries_3712_);
    v___x_3715_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3715_, 0, v___x_3714_);
    v___x_3716_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3716_, 0, v___x_3713_);
    crate::leanh::lean_ctor_set(v___x_3716_, 1, v___x_3715_);
    return v___x_3716_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___boxed(
    mut v_state_3717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3718_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg(
        v_state_3717_,
    );
    crate::leanh::lean_dec_ref(v_state_3717_);
    return v_res_3718_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn(
    mut v_pu_3719_: u8,
    mut v_00_u03b2_3720_: *mut crate::leanh::LeanObject,
    mut v_state_3721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3722_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg(
        v_state_3721_,
    );
    return v___x_3722_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___boxed(
    mut v_pu_3723_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3724_: *mut crate::leanh::LeanObject,
    mut v_state_3725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3726_: u8 = 0;
    let mut v_res_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3726_ = (crate::leanh::lean_unbox(v_pu_3723_) as u8);
    v_res_3727_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn(
        v_pu_boxed_3726_,
        v_00_u03b2_3724_,
        v_state_3725_,
    );
    crate::leanh::lean_dec_ref(v_state_3725_);
    return v_res_3727_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___redArg(
    mut v_a_3728_: *mut crate::leanh::LeanObject,
    mut v_b_3729_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_toSignature_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: u8 = 0;
    v_toSignature_3730_ = crate::leanh::lean_ctor_get(v_a_3728_, 0);
    v_toSignature_3731_ = crate::leanh::lean_ctor_get(v_b_3729_, 0);
    v_name_3732_ = crate::leanh::lean_ctor_get(v_toSignature_3730_, 0);
    v_name_3733_ = crate::leanh::lean_ctor_get(v_toSignature_3731_, 0);
    v___x_3734_ = l_Lean_Name_quickLt(v_name_3732_, v_name_3733_);
    return v___x_3734_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___redArg___boxed(
    mut v_a_3735_: *mut crate::leanh::LeanObject,
    mut v_b_3736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3737_: u8 = 0;
    let mut v_r_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3737_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___redArg(
        v_a_3735_, v_b_3736_,
    );
    crate::leanh::lean_dec_ref(v_b_3736_);
    crate::leanh::lean_dec_ref(v_a_3735_);
    v_r_3738_ = crate::leanh::lean_box((v_res_3737_) as usize);
    return v_r_3738_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt(
    mut v_pu_3739_: u8,
    mut v_a_3740_: *mut crate::leanh::LeanObject,
    mut v_b_3741_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_toSignature_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: u8 = 0;
    v_toSignature_3742_ = crate::leanh::lean_ctor_get(v_a_3740_, 0);
    v_toSignature_3743_ = crate::leanh::lean_ctor_get(v_b_3741_, 0);
    v_name_3744_ = crate::leanh::lean_ctor_get(v_toSignature_3742_, 0);
    v_name_3745_ = crate::leanh::lean_ctor_get(v_toSignature_3743_, 0);
    v___x_3746_ = l_Lean_Name_quickLt(v_name_3744_, v_name_3745_);
    return v___x_3746_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___boxed(
    mut v_pu_3747_: *mut crate::leanh::LeanObject,
    mut v_a_3748_: *mut crate::leanh::LeanObject,
    mut v_b_3749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3750_: u8 = 0;
    let mut v_res_3751_: u8 = 0;
    let mut v_r_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3750_ = (crate::leanh::lean_unbox(v_pu_3747_) as u8);
    v_res_3751_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt(
        v_pu_boxed_3750_,
        v_a_3748_,
        v_b_3749_,
    );
    crate::leanh::lean_dec_ref(v_b_3749_);
    crate::leanh::lean_dec_ref(v_a_3748_);
    v_r_3752_ = crate::leanh::lean_box((v_res_3751_) as usize);
    return v_r_3752_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f(
    mut v_pu_3754_: u8,
    mut v_decls_3755_: *mut crate::leanh::LeanObject,
    mut v_declName_3756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tmpDecl_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_3760_: u8 = 0;
    let mut v_inlineAttr_x3f_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3764_: u8 = 0;
    let mut v_levelParams_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_safe_3768_: u8 = 0;
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3771_: u8 = 0;
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: u8 = 0;
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: u8 = 0;
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tmpDecl_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3790_: u8 = 0;
    let mut v_unused_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3792_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tmpDecl_3757_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v_pu_3754_);
                v_toSignature_3758_ = crate::leanh::lean_ctor_get(v_tmpDecl_3757_, 0);
                v_value_3759_ = crate::leanh::lean_ctor_get(v_tmpDecl_3757_, 1);
                v_recursive_3760_ = crate::leanh::lean_ctor_get_uint8(
                    v_tmpDecl_3757_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_3761_ = crate::leanh::lean_ctor_get(v_tmpDecl_3757_, 2);
                v_isSharedCheck_3792_ = (!crate::leanh::lean_is_exclusive(v_tmpDecl_3757_)) as u8;
                if v_isSharedCheck_3792_ == 0 {
                    v___x_3763_ = v_tmpDecl_3757_;
                    v_isShared_3764_ = v_isSharedCheck_3792_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineAttr_x3f_3761_);
                    crate::leanh::lean_inc(v_value_3759_);
                    crate::leanh::lean_inc(v_toSignature_3758_);
                    crate::leanh::lean_dec(v_tmpDecl_3757_);
                    v___x_3763_ = crate::leanh::lean_box(0);
                    v_isShared_3764_ = v_isSharedCheck_3792_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_levelParams_3765_ = crate::leanh::lean_ctor_get(v_toSignature_3758_, 1);
                v_type_3766_ = crate::leanh::lean_ctor_get(v_toSignature_3758_, 2);
                v_params_3767_ = crate::leanh::lean_ctor_get(v_toSignature_3758_, 3);
                v_safe_3768_ = crate::leanh::lean_ctor_get_uint8(
                    v_toSignature_3758_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                );
                v_isSharedCheck_3790_ =
                    (!crate::leanh::lean_is_exclusive(v_toSignature_3758_)) as u8;
                if v_isSharedCheck_3790_ == 0 {
                    v_unused_3791_ = crate::leanh::lean_ctor_get(v_toSignature_3758_, 0);
                    crate::leanh::lean_dec(v_unused_3791_);
                    v___x_3770_ = v_toSignature_3758_;
                    v_isShared_3771_ = v_isSharedCheck_3790_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_params_3767_);
                    crate::leanh::lean_inc(v_type_3766_);
                    crate::leanh::lean_inc(v_levelParams_3765_);
                    crate::leanh::lean_dec(v_toSignature_3758_);
                    v___x_3770_ = crate::leanh::lean_box(0);
                    v_isShared_3771_ = v_isSharedCheck_3790_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3772_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3773_ = lean_array_get_size(v_decls_3755_);
                v___x_3774_ = lean_nat_dec_lt(v___x_3772_, v___x_3773_);
                if v___x_3774_ == 0 {
                    crate::leanh::lean_del_object(v___x_3770_);
                    crate::leanh::lean_dec_ref(v_params_3767_);
                    crate::leanh::lean_dec_ref(v_type_3766_);
                    crate::leanh::lean_dec(v_levelParams_3765_);
                    crate::leanh::lean_del_object(v___x_3763_);
                    crate::leanh::lean_dec(v_inlineAttr_x3f_3761_);
                    crate::leanh::lean_dec_ref(v_value_3759_);
                    crate::leanh::lean_dec(v_declName_3756_);
                    v___x_3775_ = crate::leanh::lean_box(0);
                    return v___x_3775_;
                } else {
                    v___x_3776_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3777_ = lean_nat_sub(v___x_3773_, v___x_3776_);
                    v___x_3778_ = lean_nat_dec_le(v___x_3772_, v___x_3777_);
                    if v___x_3778_ == 0 {
                        crate::leanh::lean_dec(v___x_3777_);
                        crate::leanh::lean_del_object(v___x_3770_);
                        crate::leanh::lean_dec_ref(v_params_3767_);
                        crate::leanh::lean_dec_ref(v_type_3766_);
                        crate::leanh::lean_dec(v_levelParams_3765_);
                        crate::leanh::lean_del_object(v___x_3763_);
                        crate::leanh::lean_dec(v_inlineAttr_x3f_3761_);
                        crate::leanh::lean_dec_ref(v_value_3759_);
                        crate::leanh::lean_dec(v_declName_3756_);
                        v___x_3779_ = crate::leanh::lean_box(0);
                        return v___x_3779_;
                    } else {
                        if v_isShared_3771_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3770_, 0, v_declName_3756_);
                            v___x_3781_ = v___x_3770_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3789_ =
                                crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3789_,
                                0,
                                v_declName_3756_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3789_,
                                1,
                                v_levelParams_3765_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3789_, 2, v_type_3766_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3789_, 3, v_params_3767_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_3789_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                                v_safe_3768_,
                            );
                            v___x_3781_ = v_reuseFailAlloc_3789_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_3764_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3763_, 0, v___x_3781_);
                    v_tmpDecl_3783_ = v___x_3763_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3788_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3788_, 0, v___x_3781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3788_, 1, v_value_3759_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3788_, 2, v_inlineAttr_x3f_3761_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3788_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_recursive_3760_,
                    );
                    v_tmpDecl_3783_ = v_reuseFailAlloc_3788_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3784_ = crate::leanh::lean_box((v_pu_3754_) as usize);
                v___x_3785_ = crate::leanh::lean_alloc_closure(
                    l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_3785_, 0, v___x_3784_);
                v___x_3786_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0;
                v___x_3787_ = l_Array_binSearchAux___redArg(
                    v___x_3785_,
                    v___x_3786_,
                    v_decls_3755_,
                    v_tmpDecl_3783_,
                    v___x_3772_,
                    v___x_3777_,
                );
                return v___x_3787_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___boxed(
    mut v_pu_3793_: *mut crate::leanh::LeanObject,
    mut v_decls_3794_: *mut crate::leanh::LeanObject,
    mut v_declName_3795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3796_: u8 = 0;
    let mut v_res_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3796_ = (crate::leanh::lean_unbox(v_pu_3793_) as u8);
    v_res_3797_ =
        l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f(
            v_pu_boxed_3796_,
            v_decls_3794_,
            v_declName_3795_,
        );
    crate::leanh::lean_dec_ref(v_decls_3794_);
    return v_res_3797_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0(
    mut v_x_3801_: *mut crate::leanh::LeanObject,
    mut v___y_3802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3804_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__1;
    v___x_3805_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3805_, 0, v___x_3804_);
    return v___x_3805_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___boxed(
    mut v_x_3806_: *mut crate::leanh::LeanObject,
    mut v___y_3807_: *mut crate::leanh::LeanObject,
    mut v___y_3808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3809_ =
        l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0(v_x_3806_, v___y_3807_);
    crate::leanh::lean_dec_ref(v___y_3807_);
    crate::leanh::lean_dec_ref(v_x_3806_);
    return v_res_3809_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__1(
    mut v_s_3810_: *mut crate::leanh::LeanObject,
    mut v_x_3811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_s_3810_);
    return v_s_3810_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__1___boxed(
    mut v_s_3812_: *mut crate::leanh::LeanObject,
    mut v_x_3813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3814_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__1(v_s_3812_, v_x_3813_);
    crate::leanh::lean_dec_ref(v_x_3813_);
    crate::leanh::lean_dec_ref(v_s_3812_);
    return v_res_3814_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2(
    mut v_x_3819_: *mut crate::leanh::LeanObject,
    mut v_x_3820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3821_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__1;
    return v___x_3821_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___boxed(
    mut v_x_3822_: *mut crate::leanh::LeanObject,
    mut v_x_3823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3824_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2(v_x_3822_, v_x_3823_);
    crate::leanh::lean_dec_ref(v_x_3823_);
    crate::leanh::lean_dec_ref(v_x_3822_);
    return v_res_3824_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__3(
    mut v_x_3825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3826_ = crate::leanh::lean_box(0);
    return v___x_3826_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__3___boxed(
    mut v_x_3827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3828_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__3(v_x_3827_);
    crate::leanh::lean_dec_ref(v_x_3827_);
    return v_res_3828_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3833_ = l_Lean_instInhabitedEnvExtension_default(crate::leanh::lean_box(0));
    return v___x_3833_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___f_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3834_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__3;
    v___f_3835_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__2;
    v___f_3836_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__1;
    v___f_3837_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__0;
    v___x_3838_ = crate::leanh::lean_box(0);
    v___x_3839_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__4_once
        ),
        _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__4,
    );
    v___x_3840_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3840_, 0, v___x_3839_);
    crate::leanh::lean_ctor_set(v___x_3840_, 1, v___x_3838_);
    crate::leanh::lean_ctor_set(v___x_3840_, 2, v___f_3837_);
    crate::leanh::lean_ctor_set(v___x_3840_, 3, v___f_3836_);
    crate::leanh::lean_ctor_set(v___x_3840_, 4, v___f_3835_);
    crate::leanh::lean_ctor_set(v___x_3840_, 5, v___f_3834_);
    return v___x_3840_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1(
    mut v_pu_3841_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3842_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5_once
        ),
        _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5,
    );
    return v___x_3842_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___boxed(
    mut v_pu_3843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3844_: u8 = 0;
    let mut v_res_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3844_ = (crate::leanh::lean_unbox(v_pu_3843_) as u8);
    v_res_3845_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1(v_pu_boxed_3844_);
    return v_res_3845_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedDeclExt(
    mut v_pu_3846_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3847_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5_once
        ),
        _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5,
    );
    return v___x_3847_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedDeclExt___boxed(
    mut v_pu_3848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3849_: u8 = 0;
    let mut v_res_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3849_ = (crate::leanh::lean_unbox(v_pu_3848_) as u8);
    v_res_3850_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt(v_pu_boxed_3849_);
    return v_res_3850_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3877_ = l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__10;
    v___x_3878_ = l_Lean_mkAtom(v___x_3877_);
    return v___x_3878_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3879_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12,
    );
    v___x_3880_ = l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5;
    v___x_3881_ = lean_array_push(v___x_3880_, v___x_3879_);
    return v___x_3881_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3890_ = l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__17;
    v___x_3891_ = l_Lean_mkAtom(v___x_3890_);
    return v___x_3891_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3892_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18,
    );
    v___x_3893_ = l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5;
    v___x_3894_ = lean_array_push(v___x_3893_, v___x_3892_);
    return v___x_3894_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3895_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19,
    );
    v___x_3896_ = l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16;
    v___x_3897_ = crate::leanh::lean_box(2);
    v___x_3898_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3898_, 0, v___x_3897_);
    crate::leanh::lean_ctor_set(v___x_3898_, 1, v___x_3896_);
    crate::leanh::lean_ctor_set(v___x_3898_, 2, v___x_3895_);
    return v___x_3898_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3899_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20,
    );
    v___x_3900_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13,
    );
    v___x_3901_ = lean_array_push(v___x_3900_, v___x_3899_);
    return v___x_3901_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3902_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21,
    );
    v___x_3903_ = l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11;
    v___x_3904_ = crate::leanh::lean_box(2);
    v___x_3905_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3905_, 0, v___x_3904_);
    crate::leanh::lean_ctor_set(v___x_3905_, 1, v___x_3903_);
    crate::leanh::lean_ctor_set(v___x_3905_, 2, v___x_3902_);
    return v___x_3905_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3906_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22,
    );
    v___x_3907_ = l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5;
    v___x_3908_ = lean_array_push(v___x_3907_, v___x_3906_);
    return v___x_3908_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3909_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23,
    );
    v___x_3910_ = l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__9;
    v___x_3911_ = crate::leanh::lean_box(2);
    v___x_3912_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3912_, 0, v___x_3911_);
    crate::leanh::lean_ctor_set(v___x_3912_, 1, v___x_3910_);
    crate::leanh::lean_ctor_set(v___x_3912_, 2, v___x_3909_);
    return v___x_3912_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3913_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24,
    );
    v___x_3914_ = l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5;
    v___x_3915_ = lean_array_push(v___x_3914_, v___x_3913_);
    return v___x_3915_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3916_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25,
    );
    v___x_3917_ = l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7;
    v___x_3918_ = crate::leanh::lean_box(2);
    v___x_3919_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3919_, 0, v___x_3918_);
    crate::leanh::lean_ctor_set(v___x_3919_, 1, v___x_3917_);
    crate::leanh::lean_ctor_set(v___x_3919_, 2, v___x_3916_);
    return v___x_3919_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3920_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26,
    );
    v___x_3921_ = l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5;
    v___x_3922_ = lean_array_push(v___x_3921_, v___x_3920_);
    return v___x_3922_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3923_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27,
    );
    v___x_3924_ = l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4;
    v___x_3925_ = crate::leanh::lean_box(2);
    v___x_3926_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3926_, 0, v___x_3925_);
    crate::leanh::lean_ctor_set(v___x_3926_, 1, v___x_3924_);
    crate::leanh::lean_ctor_set(v___x_3926_, 2, v___x_3923_);
    return v___x_3926_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3927_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28,
    );
    return v___x_3927_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkDeclExt___lam__0(
    mut v_s_3928_: *mut crate::leanh::LeanObject,
    mut v_decl_3929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSignature_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toSignature_3930_ = crate::leanh::lean_ctor_get(v_decl_3929_, 0);
    v_name_3931_ = crate::leanh::lean_ctor_get(v_toSignature_3930_, 0);
    crate::leanh::lean_inc(v_name_3931_);
    v___x_3932_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_s_3928_, v_name_3931_, v_decl_3929_);
    return v___x_3932_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkDeclExt___lam__1(
    mut v_x_3933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3934_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0;
    return v___x_3934_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkDeclExt___lam__1___boxed(
    mut v_x_3935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3936_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__1(v_x_3935_);
    crate::leanh::lean_dec_ref(v_x_3935_);
    return v_res_3936_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkDeclExt___lam__2(
    mut v___y_3937_: *mut crate::leanh::LeanObject,
    mut v___y_3938_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_toSignature_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: u8 = 0;
    v_toSignature_3939_ = crate::leanh::lean_ctor_get(v___y_3937_, 0);
    v_toSignature_3940_ = crate::leanh::lean_ctor_get(v___y_3938_, 0);
    v_name_3941_ = crate::leanh::lean_ctor_get(v_toSignature_3939_, 0);
    v_name_3942_ = crate::leanh::lean_ctor_get(v_toSignature_3940_, 0);
    v___x_3943_ = l_Lean_Name_quickLt(v_name_3941_, v_name_3942_);
    return v___x_3943_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkDeclExt___lam__2___boxed(
    mut v___y_3944_: *mut crate::leanh::LeanObject,
    mut v___y_3945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3946_: u8 = 0;
    let mut v_r_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3946_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__2(v___y_3944_, v___y_3945_);
    crate::leanh::lean_dec_ref(v___y_3945_);
    crate::leanh::lean_dec_ref(v___y_3944_);
    v_r_3947_ = crate::leanh::lean_box((v_res_3946_) as usize);
    return v_r_3947_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(
    mut v_env_3953_: *mut crate::leanh::LeanObject,
    mut v_phase_3954_: u8,
    mut v_as_3955_: *mut crate::leanh::LeanObject,
    mut v_i_3956_: usize,
    mut v_stop_3957_: usize,
    mut v_b_3958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: usize = 0;
    let mut v___x_3962_: usize = 0;
    let mut v___x_3964_: u8 = 0;
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_3967_: u8 = 0;
    let mut v_inlineAttr_x3f_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: u8 = 0;
    let mut v___x_3971_: u8 = 0;
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3974_: u8 = 0;
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3980_: u8 = 0;
    let mut v_unused_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3964_ = lean_usize_dec_eq(v_i_3956_, v_stop_3957_);
                if v___x_3964_ == 0 {
                    v___x_3965_ = lean_array_uget(v_as_3955_, v_i_3956_);
                    v_toSignature_3966_ = crate::leanh::lean_ctor_get(v___x_3965_, 0);
                    v_recursive_3967_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_3965_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_inlineAttr_x3f_3968_ = crate::leanh::lean_ctor_get(v___x_3965_, 2);
                    v_name_3969_ = crate::leanh::lean_ctor_get(v_toSignature_3966_, 0);
                    crate::leanh::lean_inc_ref(v_env_3953_);
                    v___x_3970_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_3953_, v_name_3969_);
                    if v___x_3970_ == 0 {
                        crate::leanh::lean_dec(v___x_3965_);
                        v___y_3960_ = v_b_3958_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_3953_);
                        v___x_3971_ = l_Lean_Compiler_LCNF_isDeclTransparent(
                            v_env_3953_,
                            v_phase_3954_,
                            v_name_3969_,
                        );
                        if v___x_3971_ == 0 {
                            crate::leanh::lean_inc(v_inlineAttr_x3f_3968_);
                            crate::leanh::lean_inc_ref(v_toSignature_3966_);
                            v_isSharedCheck_3980_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3965_)) as u8;
                            if v_isSharedCheck_3980_ == 0 {
                                v_unused_3981_ = crate::leanh::lean_ctor_get(v___x_3965_, 2);
                                crate::leanh::lean_dec(v_unused_3981_);
                                v_unused_3982_ = crate::leanh::lean_ctor_get(v___x_3965_, 1);
                                crate::leanh::lean_dec(v_unused_3982_);
                                v_unused_3983_ = crate::leanh::lean_ctor_get(v___x_3965_, 0);
                                crate::leanh::lean_dec(v_unused_3983_);
                                v___x_3973_ = v___x_3965_;
                                v_isShared_3974_ = v_isSharedCheck_3980_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3965_);
                                v___x_3973_ = crate::leanh::lean_box(0);
                                v_isShared_3974_ = v_isSharedCheck_3980_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_3984_ = lean_array_push(v_b_3958_, v___x_3965_);
                            v___y_3960_ = v___x_3984_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_3953_);
                    return v_b_3958_;
                }
            }
            1 => {
                v___x_3961_ = 1usize;
                v___x_3962_ = lean_usize_add(v_i_3956_, v___x_3961_);
                v_i_3956_ = v___x_3962_;
                v_b_3958_ = v___y_3960_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__1;
                if v_isShared_3974_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3973_, 1, v___x_3975_);
                    v___x_3977_ = v___x_3973_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3979_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_toSignature_3966_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3979_, 1, v___x_3975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3979_, 2, v_inlineAttr_x3f_3968_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3979_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_recursive_3967_,
                    );
                    v___x_3977_ = v_reuseFailAlloc_3979_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3978_ = lean_array_push(v_b_3958_, v___x_3977_);
                v___y_3960_ = v___x_3978_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___boxed(
    mut v_env_3985_: *mut crate::leanh::LeanObject,
    mut v_phase_3986_: *mut crate::leanh::LeanObject,
    mut v_as_3987_: *mut crate::leanh::LeanObject,
    mut v_i_3988_: *mut crate::leanh::LeanObject,
    mut v_stop_3989_: *mut crate::leanh::LeanObject,
    mut v_b_3990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_3991_: u8 = 0;
    let mut v_i_boxed_3992_: usize = 0;
    let mut v_stop_boxed_3993_: usize = 0;
    let mut v_res_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_3991_ = (crate::leanh::lean_unbox(v_phase_3986_) as u8);
    v_i_boxed_3992_ = crate::leanh::lean_unbox_usize(v_i_3988_);
    crate::leanh::lean_dec(v_i_3988_);
    v_stop_boxed_3993_ = crate::leanh::lean_unbox_usize(v_stop_3989_);
    crate::leanh::lean_dec(v_stop_3989_);
    v_res_3994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_3985_, v_phase_boxed_3991_, v_as_3987_, v_i_boxed_3992_, v_stop_boxed_3993_, v_b_3990_);
    crate::leanh::lean_dec_ref(v_as_3987_);
    return v_res_3994_;
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0(
    mut v_env_3995_: *mut crate::leanh::LeanObject,
    mut v_phase_3996_: u8,
    mut v___x_3997_: u8,
    mut v_as_3998_: *mut crate::leanh::LeanObject,
    mut v_start_3999_: *mut crate::leanh::LeanObject,
    mut v_stop_4000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: u8 = 0;
    v___x_4001_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0;
    v___x_4002_ = lean_nat_dec_lt(v_start_3999_, v_stop_4000_);
    if v___x_4002_ == 0 {
        crate::leanh::lean_dec_ref(v_env_3995_);
        return v___x_4001_;
    } else {
        let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4004_: u8 = 0;
        v___x_4003_ = lean_array_get_size(v_as_3998_);
        v___x_4004_ = lean_nat_dec_le(v_stop_4000_, v___x_4003_);
        if v___x_4004_ == 0 {
            let mut v___x_4005_: u8 = 0;
            v___x_4005_ = lean_nat_dec_lt(v_start_3999_, v___x_4003_);
            if v___x_4005_ == 0 {
                crate::leanh::lean_dec_ref(v_env_3995_);
                return v___x_4001_;
            } else {
                let mut v___x_4006_: usize = 0;
                let mut v___x_4007_: usize = 0;
                let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4006_ = lean_usize_of_nat(v_start_3999_);
                v___x_4007_ = lean_usize_of_nat(v___x_4003_);
                v___x_4008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_3995_, v_phase_3996_, v_as_3998_, v___x_4006_, v___x_4007_, v___x_4001_);
                return v___x_4008_;
            }
        } else {
            let mut v___x_4009_: usize = 0;
            let mut v___x_4010_: usize = 0;
            let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4009_ = lean_usize_of_nat(v_start_3999_);
            v___x_4010_ = lean_usize_of_nat(v_stop_4000_);
            v___x_4011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_3995_, v_phase_3996_, v_as_3998_, v___x_4009_, v___x_4010_, v___x_4001_);
            return v___x_4011_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0___boxed(
    mut v_env_4012_: *mut crate::leanh::LeanObject,
    mut v_phase_4013_: *mut crate::leanh::LeanObject,
    mut v___x_4014_: *mut crate::leanh::LeanObject,
    mut v_as_4015_: *mut crate::leanh::LeanObject,
    mut v_start_4016_: *mut crate::leanh::LeanObject,
    mut v_stop_4017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_4018_: u8 = 0;
    let mut v___x_1056__boxed_4019_: u8 = 0;
    let mut v_res_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_4018_ = (crate::leanh::lean_unbox(v_phase_4013_) as u8);
    v___x_1056__boxed_4019_ = (crate::leanh::lean_unbox(v___x_4014_) as u8);
    v_res_4020_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0(
        v_env_4012_,
        v_phase_boxed_4018_,
        v___x_1056__boxed_4019_,
        v_as_4015_,
        v_start_4016_,
        v_stop_4017_,
    );
    crate::leanh::lean_dec(v_stop_4017_);
    crate::leanh::lean_dec(v_start_4016_);
    crate::leanh::lean_dec_ref(v_as_4015_);
    return v_res_4020_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkDeclExt___lam__3(
    mut v_phase_4021_: u8,
    mut v___f_4022_: *mut crate::leanh::LeanObject,
    mut v_env_4023_: *mut crate::leanh::LeanObject,
    mut v_s_4024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4025_: u8 = 0;
    let mut v_all_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exported_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4025_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_4021_);
    v_all_4026_ =
        l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(
            v_s_4024_,
            v___f_4022_,
        );
    v___x_4027_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4028_ = lean_array_get_size(v_all_4026_);
    v_exported_4029_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0(
        v_env_4023_,
        v_phase_4021_,
        v___x_4025_,
        v_all_4026_,
        v___x_4027_,
        v___x_4028_,
    );
    crate::leanh::lean_inc_ref(v_exported_4029_);
    v___x_4030_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4030_, 0, v_exported_4029_);
    crate::leanh::lean_ctor_set(v___x_4030_, 1, v_exported_4029_);
    crate::leanh::lean_ctor_set(v___x_4030_, 2, v_all_4026_);
    return v___x_4030_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkDeclExt___lam__3___boxed(
    mut v_phase_4031_: *mut crate::leanh::LeanObject,
    mut v___f_4032_: *mut crate::leanh::LeanObject,
    mut v_env_4033_: *mut crate::leanh::LeanObject,
    mut v_s_4034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_4035_: u8 = 0;
    let mut v_res_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_4035_ = (crate::leanh::lean_unbox(v_phase_4031_) as u8);
    v_res_4036_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__3(
        v_phase_boxed_4035_,
        v___f_4032_,
        v_env_4033_,
        v_s_4034_,
    );
    crate::leanh::lean_dec_ref(v_s_4034_);
    return v_res_4036_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkDeclExt___lam__4(
    mut v___x_4037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4039_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4039_, 0, v___x_4037_);
    return v___x_4039_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkDeclExt___lam__4___boxed(
    mut v___x_4040_: *mut crate::leanh::LeanObject,
    mut v___y_4041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4042_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__4(v___x_4040_);
    return v_res_4042_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkDeclExt___lam__5(
    mut v___x_4043_: *mut crate::leanh::LeanObject,
    mut v_x_4044_: *mut crate::leanh::LeanObject,
    mut v___y_4045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4047_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4047_, 0, v___x_4043_);
    return v___x_4047_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkDeclExt___lam__5___boxed(
    mut v___x_4048_: *mut crate::leanh::LeanObject,
    mut v_x_4049_: *mut crate::leanh::LeanObject,
    mut v___y_4050_: *mut crate::leanh::LeanObject,
    mut v___y_4051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4052_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__5(v___x_4048_, v_x_4049_, v___y_4050_);
    crate::leanh::lean_dec_ref(v___y_4050_);
    crate::leanh::lean_dec_ref(v_x_4049_);
    return v_res_4052_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4056_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4056_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4057_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___closed__3_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__3,
    );
    v___x_4058_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4058_, 0, v___x_4057_);
    return v___x_4058_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4059_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___closed__4_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__4,
    );
    v___f_4060_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_mkDeclExt___lam__4___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4060_, 0, v___x_4059_);
    return v___f_4060_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4061_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___closed__4_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__4,
    );
    v___f_4062_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_mkDeclExt___lam__5___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4062_, 0, v___x_4061_);
    return v___f_4062_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkDeclExt(
    mut v_phase_4063_: u8,
    mut v_name_4064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: u8 = 0;
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4066_ = l_Lean_Compiler_LCNF_mkDeclExt___closed__0;
    v___f_4067_ = l_Lean_Compiler_LCNF_mkDeclExt___closed__1;
    v___f_4068_ = l_Lean_Compiler_LCNF_mkDeclExt___closed__2;
    v___x_4069_ = crate::leanh::lean_box((v_phase_4063_) as usize);
    v___f_4070_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_mkDeclExt___lam__3___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4070_, 0, v___x_4069_);
    crate::leanh::lean_closure_set(v___f_4070_, 1, v___f_4068_);
    v___f_4071_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___closed__5_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__5,
    );
    v___f_4072_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___closed__6_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__6,
    );
    v___x_4073_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_4063_);
    v___x_4074_ = crate::leanh::lean_box((v___x_4073_) as usize);
    v___x_4075_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4075_, 0, v___x_4074_);
    crate::leanh::lean_closure_set(v___x_4075_, 1, crate::leanh::lean_box(0));
    v___x_4076_ = crate::leanh::lean_box(0);
    v___x_4077_ = crate::leanh::lean_box((v_phase_4063_) as usize);
    v___x_4078_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed
            as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4078_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4078_, 1, v___x_4077_);
    v___x_4079_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4079_, 0, v___x_4078_);
    v___x_4080_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4080_, 0, v_name_4064_);
    crate::leanh::lean_ctor_set(v___x_4080_, 1, v___f_4071_);
    crate::leanh::lean_ctor_set(v___x_4080_, 2, v___f_4072_);
    crate::leanh::lean_ctor_set(v___x_4080_, 3, v___f_4066_);
    crate::leanh::lean_ctor_set(v___x_4080_, 4, v___f_4070_);
    crate::leanh::lean_ctor_set(v___x_4080_, 5, v___x_4075_);
    crate::leanh::lean_ctor_set(v___x_4080_, 6, v___x_4076_);
    crate::leanh::lean_ctor_set(v___x_4080_, 7, v___x_4079_);
    v___x_4081_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4081_, 0, v___x_4080_);
    crate::leanh::lean_ctor_set(v___x_4081_, 1, v___f_4067_);
    v___x_4082_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4081_);
    return v___x_4082_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkDeclExt___boxed(
    mut v_phase_4083_: *mut crate::leanh::LeanObject,
    mut v_name_4084_: *mut crate::leanh::LeanObject,
    mut v_a_4085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_4086_: u8 = 0;
    let mut v_res_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_4086_ = (crate::leanh::lean_unbox(v_phase_4083_) as u8);
    v_res_4087_ = l_Lean_Compiler_LCNF_mkDeclExt(v_phase_boxed_4086_, v_name_4084_);
    return v_res_4087_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0(
    mut v_env_4088_: *mut crate::leanh::LeanObject,
    mut v_phase_4089_: u8,
    mut v___x_4090_: u8,
    mut v_as_4091_: *mut crate::leanh::LeanObject,
    mut v_i_4092_: usize,
    mut v_stop_4093_: usize,
    mut v_b_4094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_4088_, v_phase_4089_, v_as_4091_, v_i_4092_, v_stop_4093_, v_b_4094_);
    return v___x_4095_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___boxed(
    mut v_env_4096_: *mut crate::leanh::LeanObject,
    mut v_phase_4097_: *mut crate::leanh::LeanObject,
    mut v___x_4098_: *mut crate::leanh::LeanObject,
    mut v_as_4099_: *mut crate::leanh::LeanObject,
    mut v_i_4100_: *mut crate::leanh::LeanObject,
    mut v_stop_4101_: *mut crate::leanh::LeanObject,
    mut v_b_4102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_4103_: u8 = 0;
    let mut v___x_1182__boxed_4104_: u8 = 0;
    let mut v_i_boxed_4105_: usize = 0;
    let mut v_stop_boxed_4106_: usize = 0;
    let mut v_res_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_4103_ = (crate::leanh::lean_unbox(v_phase_4097_) as u8);
    v___x_1182__boxed_4104_ = (crate::leanh::lean_unbox(v___x_4098_) as u8);
    v_i_boxed_4105_ = crate::leanh::lean_unbox_usize(v_i_4100_);
    crate::leanh::lean_dec(v_i_4100_);
    v_stop_boxed_4106_ = crate::leanh::lean_unbox_usize(v_stop_4101_);
    crate::leanh::lean_dec(v_stop_4101_);
    v_res_4107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0(v_env_4096_, v_phase_boxed_4103_, v___x_1182__boxed_4104_, v_as_4099_, v_i_boxed_4105_, v_stop_boxed_4106_, v_b_4102_);
    crate::leanh::lean_dec_ref(v_as_4099_);
    return v_res_4107_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4117_: u8 = 0;
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4117_ = 0;
    v___x_4118_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_;
    v___x_4119_ = l_Lean_Compiler_LCNF_mkDeclExt(v___x_4117_, v___x_4118_);
    return v___x_4119_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2____boxed(
    mut v_a_4120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4121_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_();
    return v_res_4121_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4129_: u8 = 0;
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4129_ = 1;
    v___x_4130_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_;
    v___x_4131_ = l_Lean_Compiler_LCNF_mkDeclExt(v___x_4129_, v___x_4130_);
    return v___x_4131_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2____boxed(
    mut v_a_4132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4133_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_();
    return v_res_4133_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4140_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___closed__5_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__5,
    );
    v___x_4141_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_;
    v___x_4142_ = crate::leanh::lean_box(0);
    v___x_4143_ = l_Lean_registerEnvExtension___redArg(v___f_4140_, v___x_4141_, v___x_4142_);
    return v___x_4143_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2____boxed(
    mut v_a_4144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4145_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_();
    return v_res_4145_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__0(
    mut v_x_4146_: *mut crate::leanh::LeanObject,
    mut v___y_4147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4149_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__1;
    v___x_4150_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4150_, 0, v___x_4149_);
    return v___x_4150_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__0___boxed(
    mut v_x_4151_: *mut crate::leanh::LeanObject,
    mut v___y_4152_: *mut crate::leanh::LeanObject,
    mut v___y_4153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4154_ =
        l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__0(v_x_4151_, v___y_4152_);
    crate::leanh::lean_dec_ref(v___y_4152_);
    crate::leanh::lean_dec_ref(v_x_4151_);
    return v_res_4154_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__1(
    mut v_s_4155_: *mut crate::leanh::LeanObject,
    mut v_x_4156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_s_4155_);
    return v_s_4155_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__1___boxed(
    mut v_s_4157_: *mut crate::leanh::LeanObject,
    mut v_x_4158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4159_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__1(v_s_4157_, v_x_4158_);
    crate::leanh::lean_dec_ref(v_x_4158_);
    crate::leanh::lean_dec_ref(v_s_4157_);
    return v_res_4159_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2(
    mut v_x_4164_: *mut crate::leanh::LeanObject,
    mut v_x_4165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4166_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__1;
    return v___x_4166_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___boxed(
    mut v_x_4167_: *mut crate::leanh::LeanObject,
    mut v_x_4168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4169_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2(v_x_4167_, v_x_4168_);
    crate::leanh::lean_dec_ref(v_x_4168_);
    crate::leanh::lean_dec_ref(v_x_4167_);
    return v_res_4169_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__3(
    mut v_x_4170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4171_ = crate::leanh::lean_box(0);
    return v___x_4171_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__3___boxed(
    mut v_x_4172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4173_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__3(v_x_4172_);
    crate::leanh::lean_dec_ref(v_x_4172_);
    return v_res_4173_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4178_ = l_Lean_instInhabitedEnvExtension_default(crate::leanh::lean_box(0));
    return v___x_4178_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___f_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4179_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__3;
    v___f_4180_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__2;
    v___f_4181_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__1;
    v___f_4182_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__0;
    v___x_4183_ = crate::leanh::lean_box(0);
    v___x_4184_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__4_once),
        _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__4,
    );
    v___x_4185_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4185_, 0, v___x_4184_);
    crate::leanh::lean_ctor_set(v___x_4185_, 1, v___x_4183_);
    crate::leanh::lean_ctor_set(v___x_4185_, 2, v___f_4182_);
    crate::leanh::lean_ctor_set(v___x_4185_, 3, v___f_4181_);
    crate::leanh::lean_ctor_set(v___x_4185_, 4, v___f_4180_);
    crate::leanh::lean_ctor_set(v___x_4185_, 5, v___f_4179_);
    return v___x_4185_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1(
    mut v_pu_4186_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4187_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5_once),
        _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5,
    );
    return v___x_4187_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___boxed(
    mut v_pu_4188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4189_: u8 = 0;
    let mut v_res_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4189_ = (crate::leanh::lean_unbox(v_pu_4188_) as u8);
    v_res_4190_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1(v_pu_boxed_4189_);
    return v_res_4190_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedSigExt(
    mut v_pu_4191_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4192_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5_once),
        _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5,
    );
    return v___x_4192_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedSigExt___boxed(
    mut v_pu_4193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4194_: u8 = 0;
    let mut v_res_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4194_ = (crate::leanh::lean_unbox(v_pu_4193_) as u8);
    v_res_4195_ = l_Lean_Compiler_LCNF_instInhabitedSigExt(v_pu_boxed_4194_);
    return v_res_4195_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg(
    mut v_a_4196_: *mut crate::leanh::LeanObject,
    mut v_b_4197_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: u8 = 0;
    v_name_4198_ = crate::leanh::lean_ctor_get(v_a_4196_, 0);
    v_name_4199_ = crate::leanh::lean_ctor_get(v_b_4197_, 0);
    v___x_4200_ = l_Lean_Name_quickLt(v_name_4198_, v_name_4199_);
    return v___x_4200_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg___boxed(
    mut v_a_4201_: *mut crate::leanh::LeanObject,
    mut v_b_4202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4203_: u8 = 0;
    let mut v_r_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4203_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg(
        v_a_4201_, v_b_4202_,
    );
    crate::leanh::lean_dec_ref(v_b_4202_);
    crate::leanh::lean_dec_ref(v_a_4201_);
    v_r_4204_ = crate::leanh::lean_box((v_res_4203_) as usize);
    return v_r_4204_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt(
    mut v_pu_4205_: u8,
    mut v_a_4206_: *mut crate::leanh::LeanObject,
    mut v_b_4207_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: u8 = 0;
    v_name_4208_ = crate::leanh::lean_ctor_get(v_a_4206_, 0);
    v_name_4209_ = crate::leanh::lean_ctor_get(v_b_4207_, 0);
    v___x_4210_ = l_Lean_Name_quickLt(v_name_4208_, v_name_4209_);
    return v___x_4210_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___boxed(
    mut v_pu_4211_: *mut crate::leanh::LeanObject,
    mut v_a_4212_: *mut crate::leanh::LeanObject,
    mut v_b_4213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4214_: u8 = 0;
    let mut v_res_4215_: u8 = 0;
    let mut v_r_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4214_ = (crate::leanh::lean_unbox(v_pu_4211_) as u8);
    v_res_4215_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt(
        v_pu_boxed_4214_,
        v_a_4212_,
        v_b_4213_,
    );
    crate::leanh::lean_dec_ref(v_b_4213_);
    crate::leanh::lean_dec_ref(v_a_4212_);
    v_r_4216_ = crate::leanh::lean_box((v_res_4215_) as usize);
    return v_r_4216_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f(
    mut v_pu_4218_: u8,
    mut v_sigs_4219_: *mut crate::leanh::LeanObject,
    mut v_declName_4220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tmpSig_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_safe_4225_: u8 = 0;
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4228_: u8 = 0;
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: u8 = 0;
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: u8 = 0;
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tmpSig_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4244_: u8 = 0;
    let mut v_unused_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tmpSig_4221_ = l_Lean_Compiler_LCNF_instInhabitedSignature_default(v_pu_4218_);
                v_levelParams_4222_ = crate::leanh::lean_ctor_get(v_tmpSig_4221_, 1);
                v_type_4223_ = crate::leanh::lean_ctor_get(v_tmpSig_4221_, 2);
                v_params_4224_ = crate::leanh::lean_ctor_get(v_tmpSig_4221_, 3);
                v_safe_4225_ = crate::leanh::lean_ctor_get_uint8(
                    v_tmpSig_4221_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                );
                v_isSharedCheck_4244_ = (!crate::leanh::lean_is_exclusive(v_tmpSig_4221_)) as u8;
                if v_isSharedCheck_4244_ == 0 {
                    v_unused_4245_ = crate::leanh::lean_ctor_get(v_tmpSig_4221_, 0);
                    crate::leanh::lean_dec(v_unused_4245_);
                    v___x_4227_ = v_tmpSig_4221_;
                    v_isShared_4228_ = v_isSharedCheck_4244_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_params_4224_);
                    crate::leanh::lean_inc(v_type_4223_);
                    crate::leanh::lean_inc(v_levelParams_4222_);
                    crate::leanh::lean_dec(v_tmpSig_4221_);
                    v___x_4227_ = crate::leanh::lean_box(0);
                    v_isShared_4228_ = v_isSharedCheck_4244_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4229_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4230_ = lean_array_get_size(v_sigs_4219_);
                v___x_4231_ = lean_nat_dec_lt(v___x_4229_, v___x_4230_);
                if v___x_4231_ == 0 {
                    crate::leanh::lean_del_object(v___x_4227_);
                    crate::leanh::lean_dec_ref(v_params_4224_);
                    crate::leanh::lean_dec_ref(v_type_4223_);
                    crate::leanh::lean_dec(v_levelParams_4222_);
                    crate::leanh::lean_dec(v_declName_4220_);
                    v___x_4232_ = crate::leanh::lean_box(0);
                    return v___x_4232_;
                } else {
                    v___x_4233_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4234_ = lean_nat_sub(v___x_4230_, v___x_4233_);
                    v___x_4235_ = lean_nat_dec_le(v___x_4229_, v___x_4234_);
                    if v___x_4235_ == 0 {
                        crate::leanh::lean_dec(v___x_4234_);
                        crate::leanh::lean_del_object(v___x_4227_);
                        crate::leanh::lean_dec_ref(v_params_4224_);
                        crate::leanh::lean_dec_ref(v_type_4223_);
                        crate::leanh::lean_dec(v_levelParams_4222_);
                        crate::leanh::lean_dec(v_declName_4220_);
                        v___x_4236_ = crate::leanh::lean_box(0);
                        return v___x_4236_;
                    } else {
                        if v_isShared_4228_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4227_, 0, v_declName_4220_);
                            v_tmpSig_4238_ = v___x_4227_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4243_ =
                                crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4243_,
                                0,
                                v_declName_4220_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4243_,
                                1,
                                v_levelParams_4222_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 2, v_type_4223_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 3, v_params_4224_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_4243_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                                v_safe_4225_,
                            );
                            v_tmpSig_4238_ = v_reuseFailAlloc_4243_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_4239_ = crate::leanh::lean_box((v_pu_4218_) as usize);
                v___x_4240_ = crate::leanh::lean_alloc_closure(
                    l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_4240_, 0, v___x_4239_);
                v___x_4241_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0;
                v___x_4242_ = l_Array_binSearchAux___redArg(
                    v___x_4240_,
                    v___x_4241_,
                    v_sigs_4219_,
                    v_tmpSig_4238_,
                    v___x_4229_,
                    v___x_4234_,
                );
                return v___x_4242_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___boxed(
    mut v_pu_4246_: *mut crate::leanh::LeanObject,
    mut v_sigs_4247_: *mut crate::leanh::LeanObject,
    mut v_declName_4248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4249_: u8 = 0;
    let mut v_res_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4249_ = (crate::leanh::lean_unbox(v_pu_4246_) as u8);
    v_res_4250_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f(
        v_pu_boxed_4249_,
        v_sigs_4247_,
        v_declName_4248_,
    );
    crate::leanh::lean_dec_ref(v_sigs_4247_);
    return v_res_4250_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkSigDeclExt___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4251_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28_once),
        _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28,
    );
    return v___x_4251_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkSigDeclExt___lam__0(
    mut v_s_4252_: *mut crate::leanh::LeanObject,
    mut v_sig_4253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_4254_ = crate::leanh::lean_ctor_get(v_sig_4253_, 0);
    crate::leanh::lean_inc(v_name_4254_);
    v___x_4255_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_s_4252_, v_name_4254_, v_sig_4253_);
    return v___x_4255_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1(
    mut v_x_4256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4257_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0;
    return v___x_4257_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1___boxed(
    mut v_x_4258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4259_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1(v_x_4258_);
    crate::leanh::lean_dec_ref(v_x_4258_);
    return v_res_4259_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(
    mut v___y_4260_: *mut crate::leanh::LeanObject,
    mut v___y_4261_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: u8 = 0;
    v_name_4262_ = crate::leanh::lean_ctor_get(v___y_4260_, 0);
    v_name_4263_ = crate::leanh::lean_ctor_get(v___y_4261_, 0);
    v___x_4264_ = l_Lean_Name_quickLt(v_name_4262_, v_name_4263_);
    return v___x_4264_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2___boxed(
    mut v___y_4265_: *mut crate::leanh::LeanObject,
    mut v___y_4266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4267_: u8 = 0;
    let mut v_r_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4267_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(v___y_4265_, v___y_4266_);
    crate::leanh::lean_dec_ref(v___y_4266_);
    crate::leanh::lean_dec_ref(v___y_4265_);
    v_r_4268_ = crate::leanh::lean_box((v_res_4267_) as usize);
    return v_r_4268_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(
    mut v_env_4269_: *mut crate::leanh::LeanObject,
    mut v_as_4270_: *mut crate::leanh::LeanObject,
    mut v_i_4271_: usize,
    mut v_stop_4272_: usize,
    mut v_b_4273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: usize = 0;
    let mut v___x_4277_: usize = 0;
    let mut v___x_4279_: u8 = 0;
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: u8 = 0;
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4279_ = lean_usize_dec_eq(v_i_4271_, v_stop_4272_);
                if v___x_4279_ == 0 {
                    v___x_4280_ = lean_array_uget_borrowed(v_as_4270_, v_i_4271_);
                    v_name_4281_ = crate::leanh::lean_ctor_get(v___x_4280_, 0);
                    crate::leanh::lean_inc_ref(v_env_4269_);
                    v___x_4282_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_4269_, v_name_4281_);
                    if v___x_4282_ == 0 {
                        v___y_4275_ = v_b_4273_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v___x_4280_);
                        v___x_4283_ = lean_array_push(v_b_4273_, v___x_4280_);
                        v___y_4275_ = v___x_4283_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_4269_);
                    return v_b_4273_;
                }
            }
            1 => {
                v___x_4276_ = 1usize;
                v___x_4277_ = lean_usize_add(v_i_4271_, v___x_4276_);
                v_i_4271_ = v___x_4277_;
                v_b_4273_ = v___y_4275_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0___boxed(
    mut v_env_4284_: *mut crate::leanh::LeanObject,
    mut v_as_4285_: *mut crate::leanh::LeanObject,
    mut v_i_4286_: *mut crate::leanh::LeanObject,
    mut v_stop_4287_: *mut crate::leanh::LeanObject,
    mut v_b_4288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4289_: usize = 0;
    let mut v_stop_boxed_4290_: usize = 0;
    let mut v_res_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4289_ = crate::leanh::lean_unbox_usize(v_i_4286_);
    crate::leanh::lean_dec(v_i_4286_);
    v_stop_boxed_4290_ = crate::leanh::lean_unbox_usize(v_stop_4287_);
    crate::leanh::lean_dec(v_stop_4287_);
    v_res_4291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(v_env_4284_, v_as_4285_, v_i_boxed_4289_, v_stop_boxed_4290_, v_b_4288_);
    crate::leanh::lean_dec_ref(v_as_4285_);
    return v_res_4291_;
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0(
    mut v_env_4292_: *mut crate::leanh::LeanObject,
    mut v_as_4293_: *mut crate::leanh::LeanObject,
    mut v_start_4294_: *mut crate::leanh::LeanObject,
    mut v_stop_4295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: u8 = 0;
    v___x_4296_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0;
    v___x_4297_ = lean_nat_dec_lt(v_start_4294_, v_stop_4295_);
    if v___x_4297_ == 0 {
        crate::leanh::lean_dec_ref(v_env_4292_);
        return v___x_4296_;
    } else {
        let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4299_: u8 = 0;
        v___x_4298_ = lean_array_get_size(v_as_4293_);
        v___x_4299_ = lean_nat_dec_le(v_stop_4295_, v___x_4298_);
        if v___x_4299_ == 0 {
            let mut v___x_4300_: u8 = 0;
            v___x_4300_ = lean_nat_dec_lt(v_start_4294_, v___x_4298_);
            if v___x_4300_ == 0 {
                crate::leanh::lean_dec_ref(v_env_4292_);
                return v___x_4296_;
            } else {
                let mut v___x_4301_: usize = 0;
                let mut v___x_4302_: usize = 0;
                let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4301_ = lean_usize_of_nat(v_start_4294_);
                v___x_4302_ = lean_usize_of_nat(v___x_4298_);
                v___x_4303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(v_env_4292_, v_as_4293_, v___x_4301_, v___x_4302_, v___x_4296_);
                return v___x_4303_;
            }
        } else {
            let mut v___x_4304_: usize = 0;
            let mut v___x_4305_: usize = 0;
            let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4304_ = lean_usize_of_nat(v_start_4294_);
            v___x_4305_ = lean_usize_of_nat(v_stop_4295_);
            v___x_4306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(v_env_4292_, v_as_4293_, v___x_4304_, v___x_4305_, v___x_4296_);
            return v___x_4306_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0___boxed(
    mut v_env_4307_: *mut crate::leanh::LeanObject,
    mut v_as_4308_: *mut crate::leanh::LeanObject,
    mut v_start_4309_: *mut crate::leanh::LeanObject,
    mut v_stop_4310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4311_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0(
        v_env_4307_,
        v_as_4308_,
        v_start_4309_,
        v_stop_4310_,
    );
    crate::leanh::lean_dec(v_stop_4310_);
    crate::leanh::lean_dec(v_start_4309_);
    crate::leanh::lean_dec_ref(v_as_4308_);
    return v_res_4311_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3(
    mut v___f_4312_: *mut crate::leanh::LeanObject,
    mut v_env_4313_: *mut crate::leanh::LeanObject,
    mut v_s_4314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_all_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exported_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_all_4315_ =
        l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(
            v_s_4314_,
            v___f_4312_,
        );
    v___x_4316_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4317_ = lean_array_get_size(v_all_4315_);
    v_exported_4318_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0(
        v_env_4313_,
        v_all_4315_,
        v___x_4316_,
        v___x_4317_,
    );
    crate::leanh::lean_inc_ref(v_exported_4318_);
    v___x_4319_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4319_, 0, v_exported_4318_);
    crate::leanh::lean_ctor_set(v___x_4319_, 1, v_exported_4318_);
    crate::leanh::lean_ctor_set(v___x_4319_, 2, v_all_4315_);
    return v___x_4319_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3___boxed(
    mut v___f_4320_: *mut crate::leanh::LeanObject,
    mut v_env_4321_: *mut crate::leanh::LeanObject,
    mut v_s_4322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4323_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3(v___f_4320_, v_env_4321_, v_s_4322_);
    crate::leanh::lean_dec_ref(v_s_4322_);
    return v_res_4323_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4(
    mut v___x_4324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4326_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4326_, 0, v___x_4324_);
    return v___x_4326_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4___boxed(
    mut v___x_4327_: *mut crate::leanh::LeanObject,
    mut v___y_4328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4329_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4(v___x_4327_);
    return v_res_4329_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5(
    mut v___x_4330_: *mut crate::leanh::LeanObject,
    mut v_x_4331_: *mut crate::leanh::LeanObject,
    mut v___y_4332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4334_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4334_, 0, v___x_4330_);
    return v___x_4334_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5___boxed(
    mut v___x_4335_: *mut crate::leanh::LeanObject,
    mut v_x_4336_: *mut crate::leanh::LeanObject,
    mut v___y_4337_: *mut crate::leanh::LeanObject,
    mut v___y_4338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4339_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5(v___x_4335_, v_x_4336_, v___y_4337_);
    crate::leanh::lean_dec_ref(v___y_4337_);
    crate::leanh::lean_dec_ref(v_x_4336_);
    return v_res_4339_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4345_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4345_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4346_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4_once),
        _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4,
    );
    v___x_4347_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4347_, 0, v___x_4346_);
    return v___x_4347_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4348_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5_once),
        _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5,
    );
    v___f_4349_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4349_, 0, v___x_4348_);
    return v___f_4349_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4350_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5_once),
        _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5,
    );
    v___f_4351_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4351_, 0, v___x_4350_);
    return v___f_4351_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkSigDeclExt(
    mut v_phase_4352_: u8,
    mut v_name_4353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: u8 = 0;
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4355_ = l_Lean_Compiler_LCNF_mkSigDeclExt___closed__0;
    v___f_4356_ = l_Lean_Compiler_LCNF_mkSigDeclExt___closed__1;
    v___f_4357_ = l_Lean_Compiler_LCNF_mkSigDeclExt___closed__3;
    v___f_4358_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6_once),
        _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6,
    );
    v___f_4359_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7_once),
        _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7,
    );
    v___x_4360_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_4352_);
    v___x_4361_ = crate::leanh::lean_box((v___x_4360_) as usize);
    v___x_4362_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4362_, 0, v___x_4361_);
    crate::leanh::lean_closure_set(v___x_4362_, 1, crate::leanh::lean_box(0));
    v___x_4363_ = crate::leanh::lean_box(0);
    v___x_4364_ = crate::leanh::lean_box((v_phase_4352_) as usize);
    v___x_4365_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed
            as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4365_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4365_, 1, v___x_4364_);
    v___x_4366_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4366_, 0, v___x_4365_);
    v___x_4367_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4367_, 0, v_name_4353_);
    crate::leanh::lean_ctor_set(v___x_4367_, 1, v___f_4358_);
    crate::leanh::lean_ctor_set(v___x_4367_, 2, v___f_4359_);
    crate::leanh::lean_ctor_set(v___x_4367_, 3, v___f_4355_);
    crate::leanh::lean_ctor_set(v___x_4367_, 4, v___f_4357_);
    crate::leanh::lean_ctor_set(v___x_4367_, 5, v___x_4362_);
    crate::leanh::lean_ctor_set(v___x_4367_, 6, v___x_4363_);
    crate::leanh::lean_ctor_set(v___x_4367_, 7, v___x_4366_);
    v___x_4368_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4368_, 0, v___x_4367_);
    crate::leanh::lean_ctor_set(v___x_4368_, 1, v___f_4356_);
    v___x_4369_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4368_);
    return v___x_4369_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkSigDeclExt___boxed(
    mut v_phase_4370_: *mut crate::leanh::LeanObject,
    mut v_name_4371_: *mut crate::leanh::LeanObject,
    mut v_a_4372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_4373_: u8 = 0;
    let mut v_res_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_4373_ = (crate::leanh::lean_unbox(v_phase_4370_) as u8);
    v_res_4374_ = l_Lean_Compiler_LCNF_mkSigDeclExt(v_phase_boxed_4373_, v_name_4371_);
    return v_res_4374_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4382_: u8 = 0;
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4382_ = 2;
    v___x_4383_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_;
    v___x_4384_ = l_Lean_Compiler_LCNF_mkSigDeclExt(v___x_4382_, v___x_4383_);
    return v___x_4384_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2____boxed(
    mut v_a_4385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4386_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_();
    return v_res_4386_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(
    mut v_as_4387_: *mut crate::leanh::LeanObject,
    mut v_k_4388_: *mut crate::leanh::LeanObject,
    mut v_x_4389_: *mut crate::leanh::LeanObject,
    mut v_x_4390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: u8 = 0;
    let mut v___x_4396_: u8 = 0;
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: u8 = 0;
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: u8 = 0;
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: u8 = 0;
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4391_ = lean_nat_add(v_x_4389_, v_x_4390_);
                v___x_4392_ = crate::leanh::lean_unsigned_to_nat(1);
                v_m_4393_ = lean_nat_shiftr(v___x_4391_, v___x_4392_);
                crate::leanh::lean_dec(v___x_4391_);
                v_a_4394_ = lean_array_fget_borrowed(v_as_4387_, v_m_4393_);
                v___x_4395_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__2(v_a_4394_, v_k_4388_);
                if v___x_4395_ == 0 {
                    crate::leanh::lean_dec(v_x_4390_);
                    v___x_4396_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__2(v_k_4388_, v_a_4394_);
                    if v___x_4396_ == 0 {
                        crate::leanh::lean_dec(v_m_4393_);
                        crate::leanh::lean_dec(v_x_4389_);
                        crate::leanh::lean_inc(v_a_4394_);
                        v___x_4397_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4397_, 0, v_a_4394_);
                        return v___x_4397_;
                    } else {
                        v___x_4398_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4399_ = lean_nat_dec_eq(v_m_4393_, v___x_4398_);
                        if v___x_4399_ == 0 {
                            v___x_4400_ = lean_nat_sub(v_m_4393_, v___x_4392_);
                            crate::leanh::lean_dec(v_m_4393_);
                            v___x_4401_ = lean_nat_dec_lt(v___x_4400_, v_x_4389_);
                            if v___x_4401_ == 0 {
                                v_x_4390_ = v___x_4400_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_4400_);
                                crate::leanh::lean_dec(v_x_4389_);
                                v___x_4403_ = crate::leanh::lean_box(0);
                                return v___x_4403_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_m_4393_);
                            crate::leanh::lean_dec(v_x_4389_);
                            v___x_4404_ = crate::leanh::lean_box(0);
                            return v___x_4404_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_x_4389_);
                    v___x_4405_ = lean_nat_add(v_m_4393_, v___x_4392_);
                    crate::leanh::lean_dec(v_m_4393_);
                    v___x_4406_ = lean_nat_dec_le(v___x_4405_, v_x_4390_);
                    if v___x_4406_ == 0 {
                        crate::leanh::lean_dec(v___x_4405_);
                        crate::leanh::lean_dec(v_x_4390_);
                        v___x_4407_ = crate::leanh::lean_box(0);
                        return v___x_4407_;
                    } else {
                        v_x_4389_ = v___x_4405_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg___boxed(
    mut v_as_4409_: *mut crate::leanh::LeanObject,
    mut v_k_4410_: *mut crate::leanh::LeanObject,
    mut v_x_4411_: *mut crate::leanh::LeanObject,
    mut v_x_4412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4413_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(
        v_as_4409_, v_k_4410_, v_x_4411_, v_x_4412_,
    );
    crate::leanh::lean_dec_ref(v_k_4410_);
    crate::leanh::lean_dec_ref(v_as_4409_);
    return v_res_4413_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_4414_: *mut crate::leanh::LeanObject,
    mut v_vals_4415_: *mut crate::leanh::LeanObject,
    mut v_i_4416_: *mut crate::leanh::LeanObject,
    mut v_k_4417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: u8 = 0;
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: u8 = 0;
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4418_ = lean_array_get_size(v_keys_4414_);
                v___x_4419_ = lean_nat_dec_lt(v_i_4416_, v___x_4418_);
                if v___x_4419_ == 0 {
                    crate::leanh::lean_dec(v_i_4416_);
                    v___x_4420_ = crate::leanh::lean_box(0);
                    return v___x_4420_;
                } else {
                    v_k_x27_4421_ = lean_array_fget_borrowed(v_keys_4414_, v_i_4416_);
                    v___x_4422_ = lean_name_eq(v_k_4417_, v_k_x27_4421_);
                    if v___x_4422_ == 0 {
                        v___x_4423_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4424_ = lean_nat_add(v_i_4416_, v___x_4423_);
                        crate::leanh::lean_dec(v_i_4416_);
                        v_i_4416_ = v___x_4424_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4426_ = lean_array_fget_borrowed(v_vals_4415_, v_i_4416_);
                        crate::leanh::lean_dec(v_i_4416_);
                        crate::leanh::lean_inc(v___x_4426_);
                        v___x_4427_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4427_, 0, v___x_4426_);
                        return v___x_4427_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_4428_: *mut crate::leanh::LeanObject,
    mut v_vals_4429_: *mut crate::leanh::LeanObject,
    mut v_i_4430_: *mut crate::leanh::LeanObject,
    mut v_k_4431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4432_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4428_, v_vals_4429_, v_i_4430_, v_k_4431_);
    crate::leanh::lean_dec(v_k_4431_);
    crate::leanh::lean_dec_ref(v_vals_4429_);
    crate::leanh::lean_dec_ref(v_keys_4428_);
    return v_res_4432_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(
    mut v_x_4433_: *mut crate::leanh::LeanObject,
    mut v_x_4434_: usize,
    mut v_x_4435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: usize = 0;
    let mut v___x_4439_: usize = 0;
    let mut v___x_4440_: usize = 0;
    let mut v_j_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: u8 = 0;
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: usize = 0;
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4433_) == 0 {
                    v_es_4436_ = crate::leanh::lean_ctor_get(v_x_4433_, 0);
                    v___x_4437_ = crate::leanh::lean_box(2);
                    v___x_4438_ = 5usize;
                    v___x_4439_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1);
                    v___x_4440_ = lean_usize_land(v_x_4434_, v___x_4439_);
                    v_j_4441_ = lean_usize_to_nat(v___x_4440_);
                    v___x_4442_ = lean_array_get_borrowed(v___x_4437_, v_es_4436_, v_j_4441_);
                    crate::leanh::lean_dec(v_j_4441_);
                    match crate::leanh::lean_obj_tag(v___x_4442_) {
                        0 => {
                            v_key_4443_ = crate::leanh::lean_ctor_get(v___x_4442_, 0);
                            v_val_4444_ = crate::leanh::lean_ctor_get(v___x_4442_, 1);
                            v___x_4445_ = lean_name_eq(v_x_4435_, v_key_4443_);
                            if v___x_4445_ == 0 {
                                v___x_4446_ = crate::leanh::lean_box(0);
                                return v___x_4446_;
                            } else {
                                crate::leanh::lean_inc(v_val_4444_);
                                v___x_4447_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4447_, 0, v_val_4444_);
                                return v___x_4447_;
                            }
                        }
                        1 => {
                            v_node_4448_ = crate::leanh::lean_ctor_get(v___x_4442_, 0);
                            v___x_4449_ = lean_usize_shift_right(v_x_4434_, v___x_4438_);
                            v_x_4433_ = v_node_4448_;
                            v_x_4434_ = v___x_4449_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4451_ = crate::leanh::lean_box(0);
                            return v___x_4451_;
                        }
                    }
                } else {
                    v_ks_4452_ = crate::leanh::lean_ctor_get(v_x_4433_, 0);
                    v_vs_4453_ = crate::leanh::lean_ctor_get(v_x_4433_, 1);
                    v___x_4454_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4455_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4452_, v_vs_4453_, v___x_4454_, v_x_4435_);
                    return v___x_4455_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_4456_: *mut crate::leanh::LeanObject,
    mut v_x_4457_: *mut crate::leanh::LeanObject,
    mut v_x_4458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_429__boxed_4459_: usize = 0;
    let mut v_res_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_429__boxed_4459_ = crate::leanh::lean_unbox_usize(v_x_4457_);
    crate::leanh::lean_dec(v_x_4457_);
    v_res_4460_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(v_x_4456_, v_x_429__boxed_4459_, v_x_4458_);
    crate::leanh::lean_dec(v_x_4458_);
    crate::leanh::lean_dec_ref(v_x_4456_);
    return v_res_4460_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(
    mut v_x_4461_: *mut crate::leanh::LeanObject,
    mut v_x_4462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4464_: u64 = 0;
    let mut v___x_4465_: usize = 0;
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: u64 = 0;
    let mut v_hash_4468_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4462_) == 0 {
                    v___x_4467_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
                    v___y_4464_ = v___x_4467_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4468_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_4462_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4464_ = v_hash_4468_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4465_ = lean_uint64_to_usize(v___y_4464_);
                v___x_4466_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(v_x_4461_, v___x_4465_, v_x_4462_);
                return v___x_4466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg___boxed(
    mut v_x_4469_: *mut crate::leanh::LeanObject,
    mut v_x_4470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4471_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v_x_4469_, v_x_4470_);
    crate::leanh::lean_dec(v_x_4470_);
    crate::leanh::lean_dec_ref(v_x_4469_);
    return v_res_4471_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4474_ = l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__1;
    v___x_4475_ = l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__0;
    v___x_4476_ = l_Lean_PersistentHashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4475_,
        v___x_4474_,
    );
    return v___x_4476_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getDeclCore_x3f(
    mut v_pu_4477_: u8,
    mut v_env_4478_: *mut crate::leanh::LeanObject,
    mut v_ext_4479_: *mut crate::leanh::LeanObject,
    mut v_declName_4480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tmpDecl_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_4494_: u8 = 0;
    let mut v_inlineAttr_x3f_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4498_: u8 = 0;
    let mut v_levelParams_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_safe_4502_: u8 = 0;
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4505_: u8 = 0;
    let mut v___x_4506_: u8 = 0;
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: u8 = 0;
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: u8 = 0;
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tmpDecl_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4521_: u8 = 0;
    let mut v_unused_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4523_: u8 = 0;
    let mut v_tmpDecl_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_4527_: u8 = 0;
    let mut v_inlineAttr_x3f_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4531_: u8 = 0;
    let mut v_levelParams_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_safe_4535_: u8 = 0;
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4538_: u8 = 0;
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: u8 = 0;
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: u8 = 0;
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tmpDecl_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4553_: u8 = 0;
    let mut v_unused_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4555_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4481_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2_once),
                    _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2,
                );
                v___x_4488_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4478_, v_declName_4480_);
                if crate::leanh::lean_obj_tag(v___x_4488_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_4489_ = crate::leanh::lean_ctor_get(v___x_4488_, 0);
                    crate::leanh::lean_inc(v_val_4489_);
                    crate::leanh::lean_dec_ref_known(v___x_4488_, 1);
                    v_tmpDecl_4524_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v_pu_4477_);
                    v_toSignature_4525_ = crate::leanh::lean_ctor_get(v_tmpDecl_4524_, 0);
                    v_value_4526_ = crate::leanh::lean_ctor_get(v_tmpDecl_4524_, 1);
                    v_recursive_4527_ = crate::leanh::lean_ctor_get_uint8(
                        v_tmpDecl_4524_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_inlineAttr_x3f_4528_ = crate::leanh::lean_ctor_get(v_tmpDecl_4524_, 2);
                    v_isSharedCheck_4555_ =
                        (!crate::leanh::lean_is_exclusive(v_tmpDecl_4524_)) as u8;
                    if v_isSharedCheck_4555_ == 0 {
                        v___x_4530_ = v_tmpDecl_4524_;
                        v_isShared_4531_ = v_isSharedCheck_4555_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_inlineAttr_x3f_4528_);
                        crate::leanh::lean_inc(v_value_4526_);
                        crate::leanh::lean_inc(v_toSignature_4525_);
                        crate::leanh::lean_dec(v_tmpDecl_4524_);
                        v___x_4530_ = crate::leanh::lean_box(0);
                        v_isShared_4531_ = v_isSharedCheck_4555_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_toEnvExtension_4483_ = crate::leanh::lean_ctor_get(v_ext_4479_, 0);
                v_asyncMode_4484_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4483_, 2);
                v___x_4485_ = crate::leanh::lean_box(0);
                v___x_4486_ = l_Lean_PersistentEnvExtension_getState___redArg(
                    v___x_4481_,
                    v_ext_4479_,
                    v_env_4478_,
                    v_asyncMode_4484_,
                    v___x_4485_,
                );
                v___x_4487_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_4486_, v_declName_4480_);
                crate::leanh::lean_dec(v_declName_4480_);
                crate::leanh::lean_dec(v___x_4486_);
                return v___x_4487_;
            }
            2 => {
                v_tmpDecl_4491_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v_pu_4477_);
                v_toSignature_4492_ = crate::leanh::lean_ctor_get(v_tmpDecl_4491_, 0);
                v_value_4493_ = crate::leanh::lean_ctor_get(v_tmpDecl_4491_, 1);
                v_recursive_4494_ = crate::leanh::lean_ctor_get_uint8(
                    v_tmpDecl_4491_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_4495_ = crate::leanh::lean_ctor_get(v_tmpDecl_4491_, 2);
                v_isSharedCheck_4523_ = (!crate::leanh::lean_is_exclusive(v_tmpDecl_4491_)) as u8;
                if v_isSharedCheck_4523_ == 0 {
                    v___x_4497_ = v_tmpDecl_4491_;
                    v_isShared_4498_ = v_isSharedCheck_4523_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineAttr_x3f_4495_);
                    crate::leanh::lean_inc(v_value_4493_);
                    crate::leanh::lean_inc(v_toSignature_4492_);
                    crate::leanh::lean_dec(v_tmpDecl_4491_);
                    v___x_4497_ = crate::leanh::lean_box(0);
                    v_isShared_4498_ = v_isSharedCheck_4523_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_levelParams_4499_ = crate::leanh::lean_ctor_get(v_toSignature_4492_, 1);
                v_type_4500_ = crate::leanh::lean_ctor_get(v_toSignature_4492_, 2);
                v_params_4501_ = crate::leanh::lean_ctor_get(v_toSignature_4492_, 3);
                v_safe_4502_ = crate::leanh::lean_ctor_get_uint8(
                    v_toSignature_4492_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                );
                v_isSharedCheck_4521_ =
                    (!crate::leanh::lean_is_exclusive(v_toSignature_4492_)) as u8;
                if v_isSharedCheck_4521_ == 0 {
                    v_unused_4522_ = crate::leanh::lean_ctor_get(v_toSignature_4492_, 0);
                    crate::leanh::lean_dec(v_unused_4522_);
                    v___x_4504_ = v_toSignature_4492_;
                    v_isShared_4505_ = v_isSharedCheck_4521_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_params_4501_);
                    crate::leanh::lean_inc(v_type_4500_);
                    crate::leanh::lean_inc(v_levelParams_4499_);
                    crate::leanh::lean_dec(v_toSignature_4492_);
                    v___x_4504_ = crate::leanh::lean_box(0);
                    v_isShared_4505_ = v_isSharedCheck_4521_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4506_ = 0;
                v___x_4507_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
                    v___x_4481_,
                    v_ext_4479_,
                    v_env_4478_,
                    v_val_4489_,
                    v___x_4506_,
                );
                crate::leanh::lean_dec(v_val_4489_);
                v___x_4508_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4509_ = lean_array_get_size(v___x_4507_);
                v___x_4510_ = lean_nat_dec_lt(v___x_4508_, v___x_4509_);
                if v___x_4510_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4507_);
                    crate::leanh::lean_del_object(v___x_4504_);
                    crate::leanh::lean_dec_ref(v_params_4501_);
                    crate::leanh::lean_dec_ref(v_type_4500_);
                    crate::leanh::lean_dec(v_levelParams_4499_);
                    crate::leanh::lean_del_object(v___x_4497_);
                    crate::leanh::lean_dec(v_inlineAttr_x3f_4495_);
                    crate::leanh::lean_dec_ref(v_value_4493_);
                    state = 1;
                    continue;
                } else {
                    v___x_4511_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4512_ = lean_nat_sub(v___x_4509_, v___x_4511_);
                    v___x_4513_ = lean_nat_dec_le(v___x_4508_, v___x_4512_);
                    if v___x_4513_ == 0 {
                        crate::leanh::lean_dec(v___x_4512_);
                        crate::leanh::lean_dec_ref(v___x_4507_);
                        crate::leanh::lean_del_object(v___x_4504_);
                        crate::leanh::lean_dec_ref(v_params_4501_);
                        crate::leanh::lean_dec_ref(v_type_4500_);
                        crate::leanh::lean_dec(v_levelParams_4499_);
                        crate::leanh::lean_del_object(v___x_4497_);
                        crate::leanh::lean_dec(v_inlineAttr_x3f_4495_);
                        crate::leanh::lean_dec_ref(v_value_4493_);
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_declName_4480_);
                        if v_isShared_4505_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4504_, 0, v_declName_4480_);
                            v___x_4515_ = v___x_4504_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_4520_ =
                                crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4520_,
                                0,
                                v_declName_4480_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4520_,
                                1,
                                v_levelParams_4499_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4520_, 2, v_type_4500_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4520_, 3, v_params_4501_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_4520_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                                v_safe_4502_,
                            );
                            v___x_4515_ = v_reuseFailAlloc_4520_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if v_isShared_4498_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4497_, 0, v___x_4515_);
                    v_tmpDecl_4517_ = v___x_4497_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4519_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4519_, 0, v___x_4515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4519_, 1, v_value_4493_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4519_, 2, v_inlineAttr_x3f_4495_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4519_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_recursive_4494_,
                    );
                    v_tmpDecl_4517_ = v_reuseFailAlloc_4519_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4518_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(v___x_4507_, v_tmpDecl_4517_, v___x_4508_, v___x_4512_);
                crate::leanh::lean_dec_ref(v_tmpDecl_4517_);
                crate::leanh::lean_dec_ref(v___x_4507_);
                if crate::leanh::lean_obj_tag(v___x_4518_) == 0 {
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_declName_4480_);
                    crate::leanh::lean_dec_ref(v_env_4478_);
                    return v___x_4518_;
                }
            }
            7 => {
                v_levelParams_4532_ = crate::leanh::lean_ctor_get(v_toSignature_4525_, 1);
                v_type_4533_ = crate::leanh::lean_ctor_get(v_toSignature_4525_, 2);
                v_params_4534_ = crate::leanh::lean_ctor_get(v_toSignature_4525_, 3);
                v_safe_4535_ = crate::leanh::lean_ctor_get_uint8(
                    v_toSignature_4525_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                );
                v_isSharedCheck_4553_ =
                    (!crate::leanh::lean_is_exclusive(v_toSignature_4525_)) as u8;
                if v_isSharedCheck_4553_ == 0 {
                    v_unused_4554_ = crate::leanh::lean_ctor_get(v_toSignature_4525_, 0);
                    crate::leanh::lean_dec(v_unused_4554_);
                    v___x_4537_ = v_toSignature_4525_;
                    v_isShared_4538_ = v_isSharedCheck_4553_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_params_4534_);
                    crate::leanh::lean_inc(v_type_4533_);
                    crate::leanh::lean_inc(v_levelParams_4532_);
                    crate::leanh::lean_dec(v_toSignature_4525_);
                    v___x_4537_ = crate::leanh::lean_box(0);
                    v_isShared_4538_ = v_isSharedCheck_4553_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4539_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_4481_, v_ext_4479_, v_env_4478_, v_val_4489_);
                v___x_4540_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4541_ = lean_array_get_size(v___x_4539_);
                v___x_4542_ = lean_nat_dec_lt(v___x_4540_, v___x_4541_);
                if v___x_4542_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4539_);
                    crate::leanh::lean_del_object(v___x_4537_);
                    crate::leanh::lean_dec_ref(v_params_4534_);
                    crate::leanh::lean_dec_ref(v_type_4533_);
                    crate::leanh::lean_dec(v_levelParams_4532_);
                    crate::leanh::lean_del_object(v___x_4530_);
                    crate::leanh::lean_dec(v_inlineAttr_x3f_4528_);
                    crate::leanh::lean_dec_ref(v_value_4526_);
                    state = 2;
                    continue;
                } else {
                    v___x_4543_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4544_ = lean_nat_sub(v___x_4541_, v___x_4543_);
                    v___x_4545_ = lean_nat_dec_le(v___x_4540_, v___x_4544_);
                    if v___x_4545_ == 0 {
                        crate::leanh::lean_dec(v___x_4544_);
                        crate::leanh::lean_dec_ref(v___x_4539_);
                        crate::leanh::lean_del_object(v___x_4537_);
                        crate::leanh::lean_dec_ref(v_params_4534_);
                        crate::leanh::lean_dec_ref(v_type_4533_);
                        crate::leanh::lean_dec(v_levelParams_4532_);
                        crate::leanh::lean_del_object(v___x_4530_);
                        crate::leanh::lean_dec(v_inlineAttr_x3f_4528_);
                        crate::leanh::lean_dec_ref(v_value_4526_);
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_declName_4480_);
                        if v_isShared_4538_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4537_, 0, v_declName_4480_);
                            v___x_4547_ = v___x_4537_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_4552_ =
                                crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4552_,
                                0,
                                v_declName_4480_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4552_,
                                1,
                                v_levelParams_4532_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4552_, 2, v_type_4533_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4552_, 3, v_params_4534_);
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_4552_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                                v_safe_4535_,
                            );
                            v___x_4547_ = v_reuseFailAlloc_4552_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            9 => {
                if v_isShared_4531_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4530_, 0, v___x_4547_);
                    v_tmpDecl_4549_ = v___x_4530_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4551_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4551_, 0, v___x_4547_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4551_, 1, v_value_4526_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4551_, 2, v_inlineAttr_x3f_4528_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4551_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_recursive_4527_,
                    );
                    v_tmpDecl_4549_ = v_reuseFailAlloc_4551_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_4550_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(v___x_4539_, v_tmpDecl_4549_, v___x_4540_, v___x_4544_);
                crate::leanh::lean_dec_ref(v_tmpDecl_4549_);
                crate::leanh::lean_dec_ref(v___x_4539_);
                if crate::leanh::lean_obj_tag(v___x_4550_) == 0 {
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_4489_);
                    crate::leanh::lean_dec(v_declName_4480_);
                    crate::leanh::lean_dec_ref(v_env_4478_);
                    return v___x_4550_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getDeclCore_x3f___boxed(
    mut v_pu_4556_: *mut crate::leanh::LeanObject,
    mut v_env_4557_: *mut crate::leanh::LeanObject,
    mut v_ext_4558_: *mut crate::leanh::LeanObject,
    mut v_declName_4559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4560_: u8 = 0;
    let mut v_res_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4560_ = (crate::leanh::lean_unbox(v_pu_4556_) as u8);
    v_res_4561_ = l_Lean_Compiler_LCNF_getDeclCore_x3f(
        v_pu_boxed_4560_,
        v_env_4557_,
        v_ext_4558_,
        v_declName_4559_,
    );
    crate::leanh::lean_dec_ref(v_ext_4558_);
    return v_res_4561_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0(
    mut v_00_u03b2_4562_: *mut crate::leanh::LeanObject,
    mut v_x_4563_: *mut crate::leanh::LeanObject,
    mut v_x_4564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4565_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v_x_4563_, v_x_4564_);
    return v___x_4565_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___boxed(
    mut v_00_u03b2_4566_: *mut crate::leanh::LeanObject,
    mut v_x_4567_: *mut crate::leanh::LeanObject,
    mut v_x_4568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4569_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0(
            v_00_u03b2_4566_,
            v_x_4567_,
            v_x_4568_,
        );
    crate::leanh::lean_dec(v_x_4568_);
    crate::leanh::lean_dec_ref(v_x_4567_);
    return v_res_4569_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1(
    mut v_as_4570_: *mut crate::leanh::LeanObject,
    mut v_k_4571_: *mut crate::leanh::LeanObject,
    mut v_x_4572_: *mut crate::leanh::LeanObject,
    mut v_x_4573_: *mut crate::leanh::LeanObject,
    mut v_x_4574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4575_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(
        v_as_4570_, v_k_4571_, v_x_4572_, v_x_4573_,
    );
    return v___x_4575_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___boxed(
    mut v_as_4576_: *mut crate::leanh::LeanObject,
    mut v_k_4577_: *mut crate::leanh::LeanObject,
    mut v_x_4578_: *mut crate::leanh::LeanObject,
    mut v_x_4579_: *mut crate::leanh::LeanObject,
    mut v_x_4580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4581_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1(
        v_as_4576_, v_k_4577_, v_x_4578_, v_x_4579_, v_x_4580_,
    );
    crate::leanh::lean_dec_ref(v_k_4577_);
    crate::leanh::lean_dec_ref(v_as_4576_);
    return v_res_4581_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0(
    mut v_00_u03b2_4582_: *mut crate::leanh::LeanObject,
    mut v_x_4583_: *mut crate::leanh::LeanObject,
    mut v_x_4584_: usize,
    mut v_x_4585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4586_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(v_x_4583_, v_x_4584_, v_x_4585_);
    return v___x_4586_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_4587_: *mut crate::leanh::LeanObject,
    mut v_x_4588_: *mut crate::leanh::LeanObject,
    mut v_x_4589_: *mut crate::leanh::LeanObject,
    mut v_x_4590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_639__boxed_4591_: usize = 0;
    let mut v_res_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_639__boxed_4591_ = crate::leanh::lean_unbox_usize(v_x_4589_);
    crate::leanh::lean_dec(v_x_4589_);
    v_res_4592_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0(v_00_u03b2_4587_, v_x_4588_, v_x_639__boxed_4591_, v_x_4590_);
    crate::leanh::lean_dec(v_x_4590_);
    crate::leanh::lean_dec_ref(v_x_4588_);
    return v_res_4592_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4593_: *mut crate::leanh::LeanObject,
    mut v_keys_4594_: *mut crate::leanh::LeanObject,
    mut v_vals_4595_: *mut crate::leanh::LeanObject,
    mut v_heq_4596_: *mut crate::leanh::LeanObject,
    mut v_i_4597_: *mut crate::leanh::LeanObject,
    mut v_k_4598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4599_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4594_, v_vals_4595_, v_i_4597_, v_k_4598_);
    return v___x_4599_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4600_: *mut crate::leanh::LeanObject,
    mut v_keys_4601_: *mut crate::leanh::LeanObject,
    mut v_vals_4602_: *mut crate::leanh::LeanObject,
    mut v_heq_4603_: *mut crate::leanh::LeanObject,
    mut v_i_4604_: *mut crate::leanh::LeanObject,
    mut v_k_4605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4606_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4600_, v_keys_4601_, v_vals_4602_, v_heq_4603_, v_i_4604_, v_k_4605_);
    crate::leanh::lean_dec(v_k_4605_);
    crate::leanh::lean_dec_ref(v_vals_4602_);
    crate::leanh::lean_dec_ref(v_keys_4601_);
    return v_res_4606_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(
    mut v_as_4607_: *mut crate::leanh::LeanObject,
    mut v_k_4608_: *mut crate::leanh::LeanObject,
    mut v_x_4609_: *mut crate::leanh::LeanObject,
    mut v_x_4610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: u8 = 0;
    let mut v___x_4616_: u8 = 0;
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: u8 = 0;
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: u8 = 0;
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: u8 = 0;
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4611_ = lean_nat_add(v_x_4609_, v_x_4610_);
                v___x_4612_ = crate::leanh::lean_unsigned_to_nat(1);
                v_m_4613_ = lean_nat_shiftr(v___x_4611_, v___x_4612_);
                crate::leanh::lean_dec(v___x_4611_);
                v_a_4614_ = lean_array_fget_borrowed(v_as_4607_, v_m_4613_);
                v___x_4615_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(v_a_4614_, v_k_4608_);
                if v___x_4615_ == 0 {
                    crate::leanh::lean_dec(v_x_4610_);
                    v___x_4616_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(v_k_4608_, v_a_4614_);
                    if v___x_4616_ == 0 {
                        crate::leanh::lean_dec(v_m_4613_);
                        crate::leanh::lean_dec(v_x_4609_);
                        crate::leanh::lean_inc(v_a_4614_);
                        v___x_4617_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4617_, 0, v_a_4614_);
                        return v___x_4617_;
                    } else {
                        v___x_4618_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4619_ = lean_nat_dec_eq(v_m_4613_, v___x_4618_);
                        if v___x_4619_ == 0 {
                            v___x_4620_ = lean_nat_sub(v_m_4613_, v___x_4612_);
                            crate::leanh::lean_dec(v_m_4613_);
                            v___x_4621_ = lean_nat_dec_lt(v___x_4620_, v_x_4609_);
                            if v___x_4621_ == 0 {
                                v_x_4610_ = v___x_4620_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_4620_);
                                crate::leanh::lean_dec(v_x_4609_);
                                v___x_4623_ = crate::leanh::lean_box(0);
                                return v___x_4623_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_m_4613_);
                            crate::leanh::lean_dec(v_x_4609_);
                            v___x_4624_ = crate::leanh::lean_box(0);
                            return v___x_4624_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_x_4609_);
                    v___x_4625_ = lean_nat_add(v_m_4613_, v___x_4612_);
                    crate::leanh::lean_dec(v_m_4613_);
                    v___x_4626_ = lean_nat_dec_le(v___x_4625_, v_x_4610_);
                    if v___x_4626_ == 0 {
                        crate::leanh::lean_dec(v___x_4625_);
                        crate::leanh::lean_dec(v_x_4610_);
                        v___x_4627_ = crate::leanh::lean_box(0);
                        return v___x_4627_;
                    } else {
                        v_x_4609_ = v___x_4625_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg___boxed(
    mut v_as_4629_: *mut crate::leanh::LeanObject,
    mut v_k_4630_: *mut crate::leanh::LeanObject,
    mut v_x_4631_: *mut crate::leanh::LeanObject,
    mut v_x_4632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4633_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(
        v_as_4629_, v_k_4630_, v_x_4631_, v_x_4632_,
    );
    crate::leanh::lean_dec_ref(v_k_4630_);
    crate::leanh::lean_dec_ref(v_as_4629_);
    return v_res_4633_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getSigCore_x3f___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4634_ = l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__1;
    v___x_4635_ = l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__0;
    v___x_4636_ = l_Lean_PersistentHashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4635_,
        v___x_4634_,
    );
    return v___x_4636_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getSigCore_x3f(
    mut v_pu_4637_: u8,
    mut v_env_4638_: *mut crate::leanh::LeanObject,
    mut v_ext_4639_: *mut crate::leanh::LeanObject,
    mut v_declName_4640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: u8 = 0;
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: u8 = 0;
    let mut v_tmpSig_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_safe_4660_: u8 = 0;
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4663_: u8 = 0;
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: u8 = 0;
    let mut v_tmpSig_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4671_: u8 = 0;
    let mut v_unused_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: u8 = 0;
    let mut v_tmpSig_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_safe_4681_: u8 = 0;
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4684_: u8 = 0;
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: u8 = 0;
    let mut v_tmpSig_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4692_: u8 = 0;
    let mut v_unused_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4641_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getSigCore_x3f___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getSigCore_x3f___closed__0_once),
                    _init_l_Lean_Compiler_LCNF_getSigCore_x3f___closed__0,
                );
                v___x_4648_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4638_, v_declName_4640_);
                if crate::leanh::lean_obj_tag(v___x_4648_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_4649_ = crate::leanh::lean_ctor_get(v___x_4648_, 0);
                    crate::leanh::lean_inc(v_val_4649_);
                    crate::leanh::lean_dec_ref_known(v___x_4648_, 1);
                    v___x_4673_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_4641_, v_ext_4639_, v_env_4638_, v_val_4649_);
                    v___x_4674_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4675_ = lean_array_get_size(v___x_4673_);
                    v___x_4676_ = lean_nat_dec_lt(v___x_4674_, v___x_4675_);
                    if v___x_4676_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_4673_);
                        state = 2;
                        continue;
                    } else {
                        v_tmpSig_4677_ =
                            l_Lean_Compiler_LCNF_instInhabitedSignature_default(v_pu_4637_);
                        v_levelParams_4678_ = crate::leanh::lean_ctor_get(v_tmpSig_4677_, 1);
                        v_type_4679_ = crate::leanh::lean_ctor_get(v_tmpSig_4677_, 2);
                        v_params_4680_ = crate::leanh::lean_ctor_get(v_tmpSig_4677_, 3);
                        v_safe_4681_ = crate::leanh::lean_ctor_get_uint8(
                            v_tmpSig_4677_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        );
                        v_isSharedCheck_4692_ =
                            (!crate::leanh::lean_is_exclusive(v_tmpSig_4677_)) as u8;
                        if v_isSharedCheck_4692_ == 0 {
                            v_unused_4693_ = crate::leanh::lean_ctor_get(v_tmpSig_4677_, 0);
                            crate::leanh::lean_dec(v_unused_4693_);
                            v___x_4683_ = v_tmpSig_4677_;
                            v_isShared_4684_ = v_isSharedCheck_4692_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_params_4680_);
                            crate::leanh::lean_inc(v_type_4679_);
                            crate::leanh::lean_inc(v_levelParams_4678_);
                            crate::leanh::lean_dec(v_tmpSig_4677_);
                            v___x_4683_ = crate::leanh::lean_box(0);
                            v_isShared_4684_ = v_isSharedCheck_4692_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_toEnvExtension_4643_ = crate::leanh::lean_ctor_get(v_ext_4639_, 0);
                v_asyncMode_4644_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4643_, 2);
                v___x_4645_ = crate::leanh::lean_box(0);
                v___x_4646_ = l_Lean_PersistentEnvExtension_getState___redArg(
                    v___x_4641_,
                    v_ext_4639_,
                    v_env_4638_,
                    v_asyncMode_4644_,
                    v___x_4645_,
                );
                v___x_4647_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_4646_, v_declName_4640_);
                crate::leanh::lean_dec(v_declName_4640_);
                crate::leanh::lean_dec(v___x_4646_);
                return v___x_4647_;
            }
            2 => {
                v___x_4651_ = 0;
                v___x_4652_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
                    v___x_4641_,
                    v_ext_4639_,
                    v_env_4638_,
                    v_val_4649_,
                    v___x_4651_,
                );
                crate::leanh::lean_dec(v_val_4649_);
                v___x_4653_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4654_ = lean_array_get_size(v___x_4652_);
                v___x_4655_ = lean_nat_dec_lt(v___x_4653_, v___x_4654_);
                if v___x_4655_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4652_);
                    state = 1;
                    continue;
                } else {
                    v_tmpSig_4656_ =
                        l_Lean_Compiler_LCNF_instInhabitedSignature_default(v_pu_4637_);
                    v_levelParams_4657_ = crate::leanh::lean_ctor_get(v_tmpSig_4656_, 1);
                    v_type_4658_ = crate::leanh::lean_ctor_get(v_tmpSig_4656_, 2);
                    v_params_4659_ = crate::leanh::lean_ctor_get(v_tmpSig_4656_, 3);
                    v_safe_4660_ = crate::leanh::lean_ctor_get_uint8(
                        v_tmpSig_4656_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    v_isSharedCheck_4671_ =
                        (!crate::leanh::lean_is_exclusive(v_tmpSig_4656_)) as u8;
                    if v_isSharedCheck_4671_ == 0 {
                        v_unused_4672_ = crate::leanh::lean_ctor_get(v_tmpSig_4656_, 0);
                        crate::leanh::lean_dec(v_unused_4672_);
                        v___x_4662_ = v_tmpSig_4656_;
                        v_isShared_4663_ = v_isSharedCheck_4671_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_params_4659_);
                        crate::leanh::lean_inc(v_type_4658_);
                        crate::leanh::lean_inc(v_levelParams_4657_);
                        crate::leanh::lean_dec(v_tmpSig_4656_);
                        v___x_4662_ = crate::leanh::lean_box(0);
                        v_isShared_4663_ = v_isSharedCheck_4671_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4664_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4665_ = lean_nat_sub(v___x_4654_, v___x_4664_);
                v___x_4666_ = lean_nat_dec_le(v___x_4653_, v___x_4665_);
                if v___x_4666_ == 0 {
                    crate::leanh::lean_dec(v___x_4665_);
                    crate::leanh::lean_del_object(v___x_4662_);
                    crate::leanh::lean_dec_ref(v_params_4659_);
                    crate::leanh::lean_dec_ref(v_type_4658_);
                    crate::leanh::lean_dec(v_levelParams_4657_);
                    crate::leanh::lean_dec_ref(v___x_4652_);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_declName_4640_);
                    if v_isShared_4663_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4662_, 0, v_declName_4640_);
                        v_tmpSig_4668_ = v___x_4662_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4670_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_declName_4640_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4670_, 1, v_levelParams_4657_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4670_, 2, v_type_4658_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4670_, 3, v_params_4659_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4670_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            v_safe_4660_,
                        );
                        v_tmpSig_4668_ = v_reuseFailAlloc_4670_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4669_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(v___x_4652_, v_tmpSig_4668_, v___x_4653_, v___x_4665_);
                crate::leanh::lean_dec_ref(v_tmpSig_4668_);
                crate::leanh::lean_dec_ref(v___x_4652_);
                if crate::leanh::lean_obj_tag(v___x_4669_) == 0 {
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_declName_4640_);
                    crate::leanh::lean_dec_ref(v_env_4638_);
                    return v___x_4669_;
                }
            }
            5 => {
                v___x_4685_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4686_ = lean_nat_sub(v___x_4675_, v___x_4685_);
                v___x_4687_ = lean_nat_dec_le(v___x_4674_, v___x_4686_);
                if v___x_4687_ == 0 {
                    crate::leanh::lean_dec(v___x_4686_);
                    crate::leanh::lean_del_object(v___x_4683_);
                    crate::leanh::lean_dec_ref(v_params_4680_);
                    crate::leanh::lean_dec_ref(v_type_4679_);
                    crate::leanh::lean_dec(v_levelParams_4678_);
                    crate::leanh::lean_dec_ref(v___x_4673_);
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_declName_4640_);
                    if v_isShared_4684_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4683_, 0, v_declName_4640_);
                        v_tmpSig_4689_ = v___x_4683_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4691_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4691_, 0, v_declName_4640_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4691_, 1, v_levelParams_4678_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4691_, 2, v_type_4679_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4691_, 3, v_params_4680_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4691_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            v_safe_4681_,
                        );
                        v_tmpSig_4689_ = v_reuseFailAlloc_4691_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_4690_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(v___x_4673_, v_tmpSig_4689_, v___x_4674_, v___x_4686_);
                crate::leanh::lean_dec_ref(v_tmpSig_4689_);
                crate::leanh::lean_dec_ref(v___x_4673_);
                if crate::leanh::lean_obj_tag(v___x_4690_) == 0 {
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_4649_);
                    crate::leanh::lean_dec(v_declName_4640_);
                    crate::leanh::lean_dec_ref(v_env_4638_);
                    return v___x_4690_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getSigCore_x3f___boxed(
    mut v_pu_4694_: *mut crate::leanh::LeanObject,
    mut v_env_4695_: *mut crate::leanh::LeanObject,
    mut v_ext_4696_: *mut crate::leanh::LeanObject,
    mut v_declName_4697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4698_: u8 = 0;
    let mut v_res_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4698_ = (crate::leanh::lean_unbox(v_pu_4694_) as u8);
    v_res_4699_ = l_Lean_Compiler_LCNF_getSigCore_x3f(
        v_pu_boxed_4698_,
        v_env_4695_,
        v_ext_4696_,
        v_declName_4697_,
    );
    crate::leanh::lean_dec_ref(v_ext_4696_);
    return v_res_4699_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0(
    mut v_as_4700_: *mut crate::leanh::LeanObject,
    mut v_k_4701_: *mut crate::leanh::LeanObject,
    mut v_x_4702_: *mut crate::leanh::LeanObject,
    mut v_x_4703_: *mut crate::leanh::LeanObject,
    mut v_x_4704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4705_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(
        v_as_4700_, v_k_4701_, v_x_4702_, v_x_4703_,
    );
    return v___x_4705_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___boxed(
    mut v_as_4706_: *mut crate::leanh::LeanObject,
    mut v_k_4707_: *mut crate::leanh::LeanObject,
    mut v_x_4708_: *mut crate::leanh::LeanObject,
    mut v_x_4709_: *mut crate::leanh::LeanObject,
    mut v_x_4710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4711_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0(
        v_as_4706_, v_k_4707_, v_x_4708_, v_x_4709_, v_x_4710_,
    );
    crate::leanh::lean_dec_ref(v_k_4707_);
    crate::leanh::lean_dec_ref(v_as_4706_);
    return v_res_4711_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(
    mut v_declName_4712_: *mut crate::leanh::LeanObject,
    mut v_a_4713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: u8 = 0;
    let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4715_ = lean_st_ref_get(v_a_4713_);
    v_env_4716_ = crate::leanh::lean_ctor_get(v___x_4715_, 0);
    crate::leanh::lean_inc_ref(v_env_4716_);
    crate::leanh::lean_dec(v___x_4715_);
    v___x_4717_ = 0;
    v___x_4718_ = l_Lean_Compiler_LCNF_baseExt;
    v___x_4719_ = l_Lean_Compiler_LCNF_getDeclCore_x3f(
        v___x_4717_,
        v_env_4716_,
        v___x_4718_,
        v_declName_4712_,
    );
    v___x_4720_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4720_, 0, v___x_4719_);
    return v___x_4720_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg___boxed(
    mut v_declName_4721_: *mut crate::leanh::LeanObject,
    mut v_a_4722_: *mut crate::leanh::LeanObject,
    mut v_a_4723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4724_ = l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(v_declName_4721_, v_a_4722_);
    crate::leanh::lean_dec(v_a_4722_);
    return v_res_4724_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getBaseDecl_x3f(
    mut v_declName_4725_: *mut crate::leanh::LeanObject,
    mut v_a_4726_: *mut crate::leanh::LeanObject,
    mut v_a_4727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4729_ = l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(v_declName_4725_, v_a_4727_);
    return v___x_4729_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getBaseDecl_x3f___boxed(
    mut v_declName_4730_: *mut crate::leanh::LeanObject,
    mut v_a_4731_: *mut crate::leanh::LeanObject,
    mut v_a_4732_: *mut crate::leanh::LeanObject,
    mut v_a_4733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4734_ = l_Lean_Compiler_LCNF_getBaseDecl_x3f(v_declName_4730_, v_a_4731_, v_a_4732_);
    crate::leanh::lean_dec(v_a_4732_);
    crate::leanh::lean_dec_ref(v_a_4731_);
    return v_res_4734_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(
    mut v_declName_4735_: *mut crate::leanh::LeanObject,
    mut v_a_4736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: u8 = 0;
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4738_ = lean_st_ref_get(v_a_4736_);
    v_env_4739_ = crate::leanh::lean_ctor_get(v___x_4738_, 0);
    crate::leanh::lean_inc_ref(v_env_4739_);
    crate::leanh::lean_dec(v___x_4738_);
    v___x_4740_ = 0;
    v___x_4741_ = l_Lean_Compiler_LCNF_monoExt;
    v___x_4742_ = l_Lean_Compiler_LCNF_getDeclCore_x3f(
        v___x_4740_,
        v_env_4739_,
        v___x_4741_,
        v_declName_4735_,
    );
    v___x_4743_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4743_, 0, v___x_4742_);
    return v___x_4743_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg___boxed(
    mut v_declName_4744_: *mut crate::leanh::LeanObject,
    mut v_a_4745_: *mut crate::leanh::LeanObject,
    mut v_a_4746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4747_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_4744_, v_a_4745_);
    crate::leanh::lean_dec(v_a_4745_);
    return v_res_4747_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getMonoDecl_x3f(
    mut v_declName_4748_: *mut crate::leanh::LeanObject,
    mut v_a_4749_: *mut crate::leanh::LeanObject,
    mut v_a_4750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4752_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_4748_, v_a_4750_);
    return v___x_4752_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getMonoDecl_x3f___boxed(
    mut v_declName_4753_: *mut crate::leanh::LeanObject,
    mut v_a_4754_: *mut crate::leanh::LeanObject,
    mut v_a_4755_: *mut crate::leanh::LeanObject,
    mut v_a_4756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4757_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f(v_declName_4753_, v_a_4754_, v_a_4755_);
    crate::leanh::lean_dec(v_a_4755_);
    crate::leanh::lean_dec_ref(v_a_4754_);
    return v_res_4757_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(
    mut v_declName_4758_: *mut crate::leanh::LeanObject,
    mut v_a_4759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4761_ = lean_st_ref_get(v_a_4759_);
    v_env_4762_ = crate::leanh::lean_ctor_get(v___x_4761_, 0);
    crate::leanh::lean_inc_ref(v_env_4762_);
    crate::leanh::lean_dec(v___x_4761_);
    v___x_4763_ = l_Lean_Compiler_LCNF_impureExt;
    v_asyncMode_4764_ = crate::leanh::lean_ctor_get(v___x_4763_, 2);
    v___x_4765_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2_once),
        _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2,
    );
    v___x_4766_ = crate::leanh::lean_box(0);
    v___x_4767_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_4765_,
        v___x_4763_,
        v_env_4762_,
        v_asyncMode_4764_,
        v___x_4766_,
    );
    v___x_4768_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_4767_, v_declName_4758_);
    crate::leanh::lean_dec(v___x_4767_);
    v___x_4769_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4769_, 0, v___x_4768_);
    return v___x_4769_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg___boxed(
    mut v_declName_4770_: *mut crate::leanh::LeanObject,
    mut v_a_4771_: *mut crate::leanh::LeanObject,
    mut v_a_4772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4773_ = l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(v_declName_4770_, v_a_4771_);
    crate::leanh::lean_dec(v_a_4771_);
    crate::leanh::lean_dec(v_declName_4770_);
    return v_res_4773_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f(
    mut v_declName_4774_: *mut crate::leanh::LeanObject,
    mut v_a_4775_: *mut crate::leanh::LeanObject,
    mut v_a_4776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4778_ = l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(v_declName_4774_, v_a_4776_);
    return v___x_4778_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___boxed(
    mut v_declName_4779_: *mut crate::leanh::LeanObject,
    mut v_a_4780_: *mut crate::leanh::LeanObject,
    mut v_a_4781_: *mut crate::leanh::LeanObject,
    mut v_a_4782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4783_ =
        l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f(v_declName_4779_, v_a_4780_, v_a_4781_);
    crate::leanh::lean_dec(v_a_4781_);
    crate::leanh::lean_dec_ref(v_a_4780_);
    crate::leanh::lean_dec(v_declName_4779_);
    return v_res_4783_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1(
    mut v_sz_4784_: usize,
    mut v_i_4785_: usize,
    mut v_bs_4786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4787_: u8 = 0;
    let mut v_v_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: usize = 0;
    let mut v___x_4793_: usize = 0;
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4787_ = lean_usize_dec_lt(v_i_4785_, v_sz_4784_);
                if v___x_4787_ == 0 {
                    return v_bs_4786_;
                } else {
                    v_v_4788_ = lean_array_uget_borrowed(v_bs_4786_, v_i_4785_);
                    v_fst_4789_ = crate::leanh::lean_ctor_get(v_v_4788_, 0);
                    crate::leanh::lean_inc(v_fst_4789_);
                    v___x_4790_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4791_ = lean_array_uset(v_bs_4786_, v_i_4785_, v___x_4790_);
                    v___x_4792_ = 1usize;
                    v___x_4793_ = lean_usize_add(v_i_4785_, v___x_4792_);
                    v___x_4794_ = lean_array_uset(v_bs_x27_4791_, v_i_4785_, v_fst_4789_);
                    v_i_4785_ = v___x_4793_;
                    v_bs_4786_ = v___x_4794_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1___boxed(
    mut v_sz_4796_: *mut crate::leanh::LeanObject,
    mut v_i_4797_: *mut crate::leanh::LeanObject,
    mut v_bs_4798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4799_: usize = 0;
    let mut v_i_boxed_4800_: usize = 0;
    let mut v_res_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4799_ = crate::leanh::lean_unbox_usize(v_sz_4796_);
    crate::leanh::lean_dec(v_sz_4796_);
    v_i_boxed_4800_ = crate::leanh::lean_unbox_usize(v_i_4797_);
    crate::leanh::lean_dec(v_i_4797_);
    v_res_4801_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1(v_sz_boxed_4799_, v_i_boxed_4800_, v_bs_4798_);
    return v_res_4801_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___lam__0(
    mut v_ps_4802_: *mut crate::leanh::LeanObject,
    mut v_k_4803_: *mut crate::leanh::LeanObject,
    mut v_v_4804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4805_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4805_, 0, v_k_4803_);
    crate::leanh::lean_ctor_set(v___x_4805_, 1, v_v_4804_);
    v___x_4806_ = lean_array_push(v_ps_4802_, v___x_4805_);
    return v___x_4806_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(
    mut v_m_4810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4811_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__0;
    v___x_4812_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__1;
    v___x_4813_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_m_4810_, v___f_4811_, v___x_4812_);
    return v___x_4813_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___boxed(
    mut v_m_4814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4815_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(v_m_4814_);
    crate::leanh::lean_dec_ref(v_m_4814_);
    return v_res_4815_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg(
    mut v_a_4816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4826_: usize = 0;
    let mut v___x_4827_: usize = 0;
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4818_ = lean_st_ref_get(v_a_4816_);
    v_env_4819_ = crate::leanh::lean_ctor_get(v___x_4818_, 0);
    crate::leanh::lean_inc_ref(v_env_4819_);
    crate::leanh::lean_dec(v___x_4818_);
    v___x_4820_ = l_Lean_Compiler_LCNF_impureExt;
    v_asyncMode_4821_ = crate::leanh::lean_ctor_get(v___x_4820_, 2);
    v___x_4822_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2_once),
        _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2,
    );
    v___x_4823_ = crate::leanh::lean_box(0);
    v___x_4824_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_4822_,
        v___x_4820_,
        v_env_4819_,
        v_asyncMode_4821_,
        v___x_4823_,
    );
    v___x_4825_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(v___x_4824_);
    crate::leanh::lean_dec(v___x_4824_);
    v_sz_4826_ = lean_array_size(v___x_4825_);
    v___x_4827_ = 0usize;
    v___x_4828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1(v_sz_4826_, v___x_4827_, v___x_4825_);
    v___x_4829_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4829_, 0, v___x_4828_);
    return v___x_4829_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg___boxed(
    mut v_a_4830_: *mut crate::leanh::LeanObject,
    mut v_a_4831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4832_ = l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg(v_a_4830_);
    crate::leanh::lean_dec(v_a_4830_);
    return v_res_4832_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getLocalImpureDecls(
    mut v_a_4833_: *mut crate::leanh::LeanObject,
    mut v_a_4834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4836_ = l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg(v_a_4834_);
    return v___x_4836_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getLocalImpureDecls___boxed(
    mut v_a_4837_: *mut crate::leanh::LeanObject,
    mut v_a_4838_: *mut crate::leanh::LeanObject,
    mut v_a_4839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4840_ = l_Lean_Compiler_LCNF_getLocalImpureDecls(v_a_4837_, v_a_4838_);
    crate::leanh::lean_dec(v_a_4838_);
    crate::leanh::lean_dec_ref(v_a_4837_);
    return v_res_4840_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0(
    mut v_00_u03b2_4841_: *mut crate::leanh::LeanObject,
    mut v_m_4842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4843_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(v_m_4842_);
    return v___x_4843_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___boxed(
    mut v_00_u03b2_4844_: *mut crate::leanh::LeanObject,
    mut v_m_4845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4846_ =
        l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0(
            v_00_u03b2_4844_,
            v_m_4845_,
        );
    crate::leanh::lean_dec_ref(v_m_4845_);
    return v_res_4846_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(
    mut v_declName_4847_: *mut crate::leanh::LeanObject,
    mut v_a_4848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: u8 = 0;
    let mut v___x_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4850_ = lean_st_ref_get(v_a_4848_);
    v_env_4851_ = crate::leanh::lean_ctor_get(v___x_4850_, 0);
    crate::leanh::lean_inc_ref(v_env_4851_);
    crate::leanh::lean_dec(v___x_4850_);
    v___x_4852_ = 1;
    v___x_4853_ = l_Lean_Compiler_LCNF_impureSigExt;
    v___x_4854_ = l_Lean_Compiler_LCNF_getSigCore_x3f(
        v___x_4852_,
        v_env_4851_,
        v___x_4853_,
        v_declName_4847_,
    );
    v___x_4855_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4855_, 0, v___x_4854_);
    return v___x_4855_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg___boxed(
    mut v_declName_4856_: *mut crate::leanh::LeanObject,
    mut v_a_4857_: *mut crate::leanh::LeanObject,
    mut v_a_4858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4859_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_4856_, v_a_4857_);
    crate::leanh::lean_dec(v_a_4857_);
    return v_res_4859_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getImpureSignature_x3f(
    mut v_declName_4860_: *mut crate::leanh::LeanObject,
    mut v_a_4861_: *mut crate::leanh::LeanObject,
    mut v_a_4862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4864_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_4860_, v_a_4862_);
    return v___x_4864_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getImpureSignature_x3f___boxed(
    mut v_declName_4865_: *mut crate::leanh::LeanObject,
    mut v_a_4866_: *mut crate::leanh::LeanObject,
    mut v_a_4867_: *mut crate::leanh::LeanObject,
    mut v_a_4868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4869_ =
        l_Lean_Compiler_LCNF_getImpureSignature_x3f(v_declName_4865_, v_a_4866_, v_a_4867_);
    crate::leanh::lean_dec(v_a_4867_);
    crate::leanh::lean_dec_ref(v_a_4866_);
    return v_res_4869_;
}
pub unsafe fn l_Lean_Compiler_LCNF_saveBaseDeclCore(
    mut v_env_4870_: *mut crate::leanh::LeanObject,
    mut v_decl_4871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4872_ = l_Lean_Compiler_LCNF_baseExt;
    v_toEnvExtension_4873_ = crate::leanh::lean_ctor_get(v___x_4872_, 0);
    v_asyncMode_4874_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4873_, 2);
    v___x_4875_ = crate::leanh::lean_box(0);
    v___x_4876_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
        v___x_4872_,
        v_env_4870_,
        v_decl_4871_,
        v_asyncMode_4874_,
        v___x_4875_,
    );
    return v___x_4876_;
}
pub unsafe fn l_Lean_Compiler_LCNF_saveMonoDeclCore(
    mut v_env_4877_: *mut crate::leanh::LeanObject,
    mut v_decl_4878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4879_ = l_Lean_Compiler_LCNF_monoExt;
    v_toEnvExtension_4880_ = crate::leanh::lean_ctor_get(v___x_4879_, 0);
    v_asyncMode_4881_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4880_, 2);
    v___x_4882_ = crate::leanh::lean_box(0);
    v___x_4883_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
        v___x_4879_,
        v_env_4877_,
        v_decl_4878_,
        v_asyncMode_4881_,
        v___x_4882_,
    );
    return v___x_4883_;
}
pub unsafe fn l_Lean_Compiler_LCNF_saveImpureDeclCore___lam__0(
    mut v_toSignature_4884_: *mut crate::leanh::LeanObject,
    mut v_decl_4885_: *mut crate::leanh::LeanObject,
    mut v_s_4886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_4887_ = crate::leanh::lean_ctor_get(v_toSignature_4884_, 0);
    crate::leanh::lean_inc(v_name_4887_);
    crate::leanh::lean_dec_ref(v_toSignature_4884_);
    v___x_4888_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_s_4886_, v_name_4887_, v_decl_4885_);
    return v___x_4888_;
}
pub unsafe fn l_Lean_Compiler_LCNF_saveImpureDeclCore(
    mut v_env_4889_: *mut crate::leanh::LeanObject,
    mut v_decl_4890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4891_ = l_Lean_Compiler_LCNF_impureExt;
    v_asyncMode_4892_ = crate::leanh::lean_ctor_get(v___x_4891_, 2);
    v_toSignature_4893_ = crate::leanh::lean_ctor_get(v_decl_4890_, 0);
    crate::leanh::lean_inc_ref_n(v_toSignature_4893_, 2);
    v___x_4894_ = l_Lean_Compiler_LCNF_impureSigExt;
    v_toEnvExtension_4895_ = crate::leanh::lean_ctor_get(v___x_4894_, 0);
    v_asyncMode_4896_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4895_, 2);
    v___f_4897_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_saveImpureDeclCore___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4897_, 0, v_toSignature_4893_);
    crate::leanh::lean_closure_set(v___f_4897_, 1, v_decl_4890_);
    v___x_4898_ = crate::leanh::lean_box(0);
    v_env_4899_ = l_Lean_EnvExtension_modifyState___redArg(
        v___x_4891_,
        v_env_4889_,
        v___f_4897_,
        v_asyncMode_4892_,
        v___x_4898_,
    );
    v___x_4900_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
        v___x_4894_,
        v_env_4899_,
        v_toSignature_4893_,
        v_asyncMode_4896_,
        v___x_4898_,
    );
    return v___x_4900_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4901_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4901_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4902_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0_once),
        _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0,
    );
    v___x_4903_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4903_, 0, v___x_4902_);
    return v___x_4903_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4904_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1_once),
        _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1,
    );
    v___x_4905_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4905_, 0, v___x_4904_);
    crate::leanh::lean_ctor_set(v___x_4905_, 1, v___x_4904_);
    return v___x_4905_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_saveBase___redArg(
    mut v_decl_4906_: *mut crate::leanh::LeanObject,
    mut v_a_4907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4920_: u8 = 0;
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4929_: u8 = 0;
    let mut v_unused_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4909_ = lean_st_ref_take(v_a_4907_);
                v_env_4910_ = crate::leanh::lean_ctor_get(v___x_4909_, 0);
                v_nextMacroScope_4911_ = crate::leanh::lean_ctor_get(v___x_4909_, 1);
                v_ngen_4912_ = crate::leanh::lean_ctor_get(v___x_4909_, 2);
                v_auxDeclNGen_4913_ = crate::leanh::lean_ctor_get(v___x_4909_, 3);
                v_traceState_4914_ = crate::leanh::lean_ctor_get(v___x_4909_, 4);
                v_messages_4915_ = crate::leanh::lean_ctor_get(v___x_4909_, 6);
                v_infoState_4916_ = crate::leanh::lean_ctor_get(v___x_4909_, 7);
                v_snapshotTasks_4917_ = crate::leanh::lean_ctor_get(v___x_4909_, 8);
                v_isSharedCheck_4929_ = (!crate::leanh::lean_is_exclusive(v___x_4909_)) as u8;
                if v_isSharedCheck_4929_ == 0 {
                    v_unused_4930_ = crate::leanh::lean_ctor_get(v___x_4909_, 5);
                    crate::leanh::lean_dec(v_unused_4930_);
                    v___x_4919_ = v___x_4909_;
                    v_isShared_4920_ = v_isSharedCheck_4929_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4917_);
                    crate::leanh::lean_inc(v_infoState_4916_);
                    crate::leanh::lean_inc(v_messages_4915_);
                    crate::leanh::lean_inc(v_traceState_4914_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4913_);
                    crate::leanh::lean_inc(v_ngen_4912_);
                    crate::leanh::lean_inc(v_nextMacroScope_4911_);
                    crate::leanh::lean_inc(v_env_4910_);
                    crate::leanh::lean_dec(v___x_4909_);
                    v___x_4919_ = crate::leanh::lean_box(0);
                    v_isShared_4920_ = v_isSharedCheck_4929_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4921_ = l_Lean_Compiler_LCNF_saveBaseDeclCore(v_env_4910_, v_decl_4906_);
                v___x_4922_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2,
                );
                if v_isShared_4920_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4919_, 5, v___x_4922_);
                    crate::leanh::lean_ctor_set(v___x_4919_, 0, v___x_4921_);
                    v___x_4924_ = v___x_4919_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4928_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4928_, 0, v___x_4921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4928_, 1, v_nextMacroScope_4911_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4928_, 2, v_ngen_4912_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4928_, 3, v_auxDeclNGen_4913_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4928_, 4, v_traceState_4914_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4928_, 5, v___x_4922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4928_, 6, v_messages_4915_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4928_, 7, v_infoState_4916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4928_, 8, v_snapshotTasks_4917_);
                    v___x_4924_ = v_reuseFailAlloc_4928_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4925_ = lean_st_ref_set(v_a_4907_, v___x_4924_);
                v___x_4926_ = crate::leanh::lean_box(0);
                v___x_4927_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4927_, 0, v___x_4926_);
                return v___x_4927_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_saveBase___redArg___boxed(
    mut v_decl_4931_: *mut crate::leanh::LeanObject,
    mut v_a_4932_: *mut crate::leanh::LeanObject,
    mut v_a_4933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4934_ = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v_decl_4931_, v_a_4932_);
    crate::leanh::lean_dec(v_a_4932_);
    return v_res_4934_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_saveBase(
    mut v_decl_4935_: *mut crate::leanh::LeanObject,
    mut v_a_4936_: *mut crate::leanh::LeanObject,
    mut v_a_4937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4939_ = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v_decl_4935_, v_a_4937_);
    return v___x_4939_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_saveBase___boxed(
    mut v_decl_4940_: *mut crate::leanh::LeanObject,
    mut v_a_4941_: *mut crate::leanh::LeanObject,
    mut v_a_4942_: *mut crate::leanh::LeanObject,
    mut v_a_4943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4944_ = l_Lean_Compiler_LCNF_Decl_saveBase(v_decl_4940_, v_a_4941_, v_a_4942_);
    crate::leanh::lean_dec(v_a_4942_);
    crate::leanh::lean_dec_ref(v_a_4941_);
    return v_res_4944_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_saveMono___redArg(
    mut v_decl_4945_: *mut crate::leanh::LeanObject,
    mut v_a_4946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4959_: u8 = 0;
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4968_: u8 = 0;
    let mut v_unused_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4948_ = lean_st_ref_take(v_a_4946_);
                v_env_4949_ = crate::leanh::lean_ctor_get(v___x_4948_, 0);
                v_nextMacroScope_4950_ = crate::leanh::lean_ctor_get(v___x_4948_, 1);
                v_ngen_4951_ = crate::leanh::lean_ctor_get(v___x_4948_, 2);
                v_auxDeclNGen_4952_ = crate::leanh::lean_ctor_get(v___x_4948_, 3);
                v_traceState_4953_ = crate::leanh::lean_ctor_get(v___x_4948_, 4);
                v_messages_4954_ = crate::leanh::lean_ctor_get(v___x_4948_, 6);
                v_infoState_4955_ = crate::leanh::lean_ctor_get(v___x_4948_, 7);
                v_snapshotTasks_4956_ = crate::leanh::lean_ctor_get(v___x_4948_, 8);
                v_isSharedCheck_4968_ = (!crate::leanh::lean_is_exclusive(v___x_4948_)) as u8;
                if v_isSharedCheck_4968_ == 0 {
                    v_unused_4969_ = crate::leanh::lean_ctor_get(v___x_4948_, 5);
                    crate::leanh::lean_dec(v_unused_4969_);
                    v___x_4958_ = v___x_4948_;
                    v_isShared_4959_ = v_isSharedCheck_4968_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4956_);
                    crate::leanh::lean_inc(v_infoState_4955_);
                    crate::leanh::lean_inc(v_messages_4954_);
                    crate::leanh::lean_inc(v_traceState_4953_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4952_);
                    crate::leanh::lean_inc(v_ngen_4951_);
                    crate::leanh::lean_inc(v_nextMacroScope_4950_);
                    crate::leanh::lean_inc(v_env_4949_);
                    crate::leanh::lean_dec(v___x_4948_);
                    v___x_4958_ = crate::leanh::lean_box(0);
                    v_isShared_4959_ = v_isSharedCheck_4968_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4960_ = l_Lean_Compiler_LCNF_saveMonoDeclCore(v_env_4949_, v_decl_4945_);
                v___x_4961_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2,
                );
                if v_isShared_4959_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4958_, 5, v___x_4961_);
                    crate::leanh::lean_ctor_set(v___x_4958_, 0, v___x_4960_);
                    v___x_4963_ = v___x_4958_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4967_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4967_, 0, v___x_4960_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4967_, 1, v_nextMacroScope_4950_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4967_, 2, v_ngen_4951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4967_, 3, v_auxDeclNGen_4952_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4967_, 4, v_traceState_4953_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4967_, 5, v___x_4961_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4967_, 6, v_messages_4954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4967_, 7, v_infoState_4955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4967_, 8, v_snapshotTasks_4956_);
                    v___x_4963_ = v_reuseFailAlloc_4967_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4964_ = lean_st_ref_set(v_a_4946_, v___x_4963_);
                v___x_4965_ = crate::leanh::lean_box(0);
                v___x_4966_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4966_, 0, v___x_4965_);
                return v___x_4966_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_saveMono___redArg___boxed(
    mut v_decl_4970_: *mut crate::leanh::LeanObject,
    mut v_a_4971_: *mut crate::leanh::LeanObject,
    mut v_a_4972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4973_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v_decl_4970_, v_a_4971_);
    crate::leanh::lean_dec(v_a_4971_);
    return v_res_4973_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_saveMono(
    mut v_decl_4974_: *mut crate::leanh::LeanObject,
    mut v_a_4975_: *mut crate::leanh::LeanObject,
    mut v_a_4976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4978_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v_decl_4974_, v_a_4976_);
    return v___x_4978_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_saveMono___boxed(
    mut v_decl_4979_: *mut crate::leanh::LeanObject,
    mut v_a_4980_: *mut crate::leanh::LeanObject,
    mut v_a_4981_: *mut crate::leanh::LeanObject,
    mut v_a_4982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4983_ = l_Lean_Compiler_LCNF_Decl_saveMono(v_decl_4979_, v_a_4980_, v_a_4981_);
    crate::leanh::lean_dec(v_a_4981_);
    crate::leanh::lean_dec_ref(v_a_4980_);
    return v_res_4983_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(
    mut v_decl_4984_: *mut crate::leanh::LeanObject,
    mut v_a_4985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4998_: u8 = 0;
    let mut v___x_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5007_: u8 = 0;
    let mut v_unused_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4987_ = lean_st_ref_take(v_a_4985_);
                v_env_4988_ = crate::leanh::lean_ctor_get(v___x_4987_, 0);
                v_nextMacroScope_4989_ = crate::leanh::lean_ctor_get(v___x_4987_, 1);
                v_ngen_4990_ = crate::leanh::lean_ctor_get(v___x_4987_, 2);
                v_auxDeclNGen_4991_ = crate::leanh::lean_ctor_get(v___x_4987_, 3);
                v_traceState_4992_ = crate::leanh::lean_ctor_get(v___x_4987_, 4);
                v_messages_4993_ = crate::leanh::lean_ctor_get(v___x_4987_, 6);
                v_infoState_4994_ = crate::leanh::lean_ctor_get(v___x_4987_, 7);
                v_snapshotTasks_4995_ = crate::leanh::lean_ctor_get(v___x_4987_, 8);
                v_isSharedCheck_5007_ = (!crate::leanh::lean_is_exclusive(v___x_4987_)) as u8;
                if v_isSharedCheck_5007_ == 0 {
                    v_unused_5008_ = crate::leanh::lean_ctor_get(v___x_4987_, 5);
                    crate::leanh::lean_dec(v_unused_5008_);
                    v___x_4997_ = v___x_4987_;
                    v_isShared_4998_ = v_isSharedCheck_5007_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4995_);
                    crate::leanh::lean_inc(v_infoState_4994_);
                    crate::leanh::lean_inc(v_messages_4993_);
                    crate::leanh::lean_inc(v_traceState_4992_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4991_);
                    crate::leanh::lean_inc(v_ngen_4990_);
                    crate::leanh::lean_inc(v_nextMacroScope_4989_);
                    crate::leanh::lean_inc(v_env_4988_);
                    crate::leanh::lean_dec(v___x_4987_);
                    v___x_4997_ = crate::leanh::lean_box(0);
                    v_isShared_4998_ = v_isSharedCheck_5007_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4999_ = l_Lean_Compiler_LCNF_saveImpureDeclCore(v_env_4988_, v_decl_4984_);
                v___x_5000_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2,
                );
                if v_isShared_4998_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4997_, 5, v___x_5000_);
                    crate::leanh::lean_ctor_set(v___x_4997_, 0, v___x_4999_);
                    v___x_5002_ = v___x_4997_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5006_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 0, v___x_4999_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 1, v_nextMacroScope_4989_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 2, v_ngen_4990_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 3, v_auxDeclNGen_4991_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 4, v_traceState_4992_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 5, v___x_5000_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 6, v_messages_4993_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 7, v_infoState_4994_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 8, v_snapshotTasks_4995_);
                    v___x_5002_ = v_reuseFailAlloc_5006_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5003_ = lean_st_ref_set(v_a_4985_, v___x_5002_);
                v___x_5004_ = crate::leanh::lean_box(0);
                v___x_5005_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5005_, 0, v___x_5004_);
                return v___x_5005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_saveImpure___redArg___boxed(
    mut v_decl_5009_: *mut crate::leanh::LeanObject,
    mut v_a_5010_: *mut crate::leanh::LeanObject,
    mut v_a_5011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5012_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_decl_5009_, v_a_5010_);
    crate::leanh::lean_dec(v_a_5010_);
    return v_res_5012_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_saveImpure(
    mut v_decl_5013_: *mut crate::leanh::LeanObject,
    mut v_a_5014_: *mut crate::leanh::LeanObject,
    mut v_a_5015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5017_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_decl_5013_, v_a_5015_);
    return v___x_5017_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_saveImpure___boxed(
    mut v_decl_5018_: *mut crate::leanh::LeanObject,
    mut v_a_5019_: *mut crate::leanh::LeanObject,
    mut v_a_5020_: *mut crate::leanh::LeanObject,
    mut v_a_5021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5022_ = l_Lean_Compiler_LCNF_Decl_saveImpure(v_decl_5018_, v_a_5019_, v_a_5020_);
    crate::leanh::lean_dec(v_a_5020_);
    crate::leanh::lean_dec_ref(v_a_5019_);
    return v_res_5022_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_save___lam__0(
    mut v_decl_5023_: *mut crate::leanh::LeanObject,
    mut v_h_5024_: *mut crate::leanh::LeanObject,
    mut v___y_5025_: *mut crate::leanh::LeanObject,
    mut v___y_5026_: *mut crate::leanh::LeanObject,
    mut v___y_5027_: *mut crate::leanh::LeanObject,
    mut v___y_5028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5030_ = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v_decl_5023_, v___y_5028_);
    return v___x_5030_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_save___lam__0___boxed(
    mut v_decl_5031_: *mut crate::leanh::LeanObject,
    mut v_h_5032_: *mut crate::leanh::LeanObject,
    mut v___y_5033_: *mut crate::leanh::LeanObject,
    mut v___y_5034_: *mut crate::leanh::LeanObject,
    mut v___y_5035_: *mut crate::leanh::LeanObject,
    mut v___y_5036_: *mut crate::leanh::LeanObject,
    mut v___y_5037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5038_ = l_Lean_Compiler_LCNF_Decl_save___lam__0(
        v_decl_5031_,
        v_h_5032_,
        v___y_5033_,
        v___y_5034_,
        v___y_5035_,
        v___y_5036_,
    );
    crate::leanh::lean_dec(v___y_5036_);
    crate::leanh::lean_dec_ref(v___y_5035_);
    crate::leanh::lean_dec(v___y_5034_);
    crate::leanh::lean_dec_ref(v___y_5033_);
    return v_res_5038_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_save___lam__1(
    mut v_decl_5039_: *mut crate::leanh::LeanObject,
    mut v_h_5040_: *mut crate::leanh::LeanObject,
    mut v___y_5041_: *mut crate::leanh::LeanObject,
    mut v___y_5042_: *mut crate::leanh::LeanObject,
    mut v___y_5043_: *mut crate::leanh::LeanObject,
    mut v___y_5044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5046_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v_decl_5039_, v___y_5044_);
    return v___x_5046_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_save___lam__1___boxed(
    mut v_decl_5047_: *mut crate::leanh::LeanObject,
    mut v_h_5048_: *mut crate::leanh::LeanObject,
    mut v___y_5049_: *mut crate::leanh::LeanObject,
    mut v___y_5050_: *mut crate::leanh::LeanObject,
    mut v___y_5051_: *mut crate::leanh::LeanObject,
    mut v___y_5052_: *mut crate::leanh::LeanObject,
    mut v___y_5053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5054_ = l_Lean_Compiler_LCNF_Decl_save___lam__1(
        v_decl_5047_,
        v_h_5048_,
        v___y_5049_,
        v___y_5050_,
        v___y_5051_,
        v___y_5052_,
    );
    crate::leanh::lean_dec(v___y_5052_);
    crate::leanh::lean_dec_ref(v___y_5051_);
    crate::leanh::lean_dec(v___y_5050_);
    crate::leanh::lean_dec_ref(v___y_5049_);
    return v_res_5054_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_save___lam__2(
    mut v_decl_5055_: *mut crate::leanh::LeanObject,
    mut v_h_5056_: *mut crate::leanh::LeanObject,
    mut v___y_5057_: *mut crate::leanh::LeanObject,
    mut v___y_5058_: *mut crate::leanh::LeanObject,
    mut v___y_5059_: *mut crate::leanh::LeanObject,
    mut v___y_5060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5062_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_decl_5055_, v___y_5060_);
    return v___x_5062_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_save___lam__2___boxed(
    mut v_decl_5063_: *mut crate::leanh::LeanObject,
    mut v_h_5064_: *mut crate::leanh::LeanObject,
    mut v___y_5065_: *mut crate::leanh::LeanObject,
    mut v___y_5066_: *mut crate::leanh::LeanObject,
    mut v___y_5067_: *mut crate::leanh::LeanObject,
    mut v___y_5068_: *mut crate::leanh::LeanObject,
    mut v___y_5069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5070_ = l_Lean_Compiler_LCNF_Decl_save___lam__2(
        v_decl_5063_,
        v_h_5064_,
        v___y_5065_,
        v___y_5066_,
        v___y_5067_,
        v___y_5068_,
    );
    crate::leanh::lean_dec(v___y_5068_);
    crate::leanh::lean_dec_ref(v___y_5067_);
    crate::leanh::lean_dec(v___y_5066_);
    crate::leanh::lean_dec_ref(v___y_5065_);
    return v_res_5070_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_save___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5071_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_5071_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_save___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5072_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_save___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_save___closed__0_once),
        _init_l_Lean_Compiler_LCNF_Decl_save___closed__0,
    );
    v___x_5073_ = l_StateRefT_x27_instMonad___redArg(v___x_5072_);
    return v___x_5073_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_save(
    mut v_pu_5076_: u8,
    mut v_decl_5077_: *mut crate::leanh::LeanObject,
    mut v_a_5078_: *mut crate::leanh::LeanObject,
    mut v_a_5079_: *mut crate::leanh::LeanObject,
    mut v_a_5080_: *mut crate::leanh::LeanObject,
    mut v_a_5081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: u8 = 0;
    let mut v___f_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: u8 = 0;
    let mut v___x_380__overap_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: u8 = 0;
    let mut v___x_398__overap_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: u8 = 0;
    let mut v___x_416__overap_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5121_: u8 = 0;
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5083_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_save___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_save___closed__1_once),
                    _init_l_Lean_Compiler_LCNF_Decl_save___closed__1,
                );
                v_toApplicative_5084_ = crate::leanh::lean_ctor_get(v___x_5083_, 0);
                v_toFunctor_5085_ = crate::leanh::lean_ctor_get(v_toApplicative_5084_, 0);
                v_toSeq_5086_ = crate::leanh::lean_ctor_get(v_toApplicative_5084_, 2);
                v_toSeqLeft_5087_ = crate::leanh::lean_ctor_get(v_toApplicative_5084_, 3);
                v_toSeqRight_5088_ = crate::leanh::lean_ctor_get(v_toApplicative_5084_, 4);
                v___f_5089_ = l_Lean_Compiler_LCNF_Decl_save___closed__2;
                v___f_5090_ = l_Lean_Compiler_LCNF_Decl_save___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_5085_, 2);
                v___f_5091_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5091_, 0, v_toFunctor_5085_);
                v___f_5092_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5092_, 0, v_toFunctor_5085_);
                v___x_5093_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5093_, 0, v___f_5091_);
                crate::leanh::lean_ctor_set(v___x_5093_, 1, v___f_5092_);
                crate::leanh::lean_inc(v_toSeqRight_5088_);
                v___f_5094_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5094_, 0, v_toSeqRight_5088_);
                crate::leanh::lean_inc(v_toSeqLeft_5087_);
                v___f_5095_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5095_, 0, v_toSeqLeft_5087_);
                crate::leanh::lean_inc(v_toSeq_5086_);
                v___f_5096_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5096_, 0, v_toSeq_5086_);
                v___x_5097_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5097_, 0, v___x_5093_);
                crate::leanh::lean_ctor_set(v___x_5097_, 1, v___f_5089_);
                crate::leanh::lean_ctor_set(v___x_5097_, 2, v___f_5096_);
                crate::leanh::lean_ctor_set(v___x_5097_, 3, v___f_5095_);
                crate::leanh::lean_ctor_set(v___x_5097_, 4, v___f_5094_);
                v___x_5098_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5098_, 0, v___x_5097_);
                crate::leanh::lean_ctor_set(v___x_5098_, 1, v___f_5090_);
                v___x_5099_ = l_StateRefT_x27_instMonad___redArg(v___x_5098_);
                v___x_5100_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_5078_);
                if crate::leanh::lean_obj_tag(v___x_5100_) == 0 {
                    v_a_5101_ = crate::leanh::lean_ctor_get(v___x_5100_, 0);
                    crate::leanh::lean_inc(v_a_5101_);
                    crate::leanh::lean_dec_ref_known(v___x_5100_, 1);
                    v___x_5102_ = crate::leanh::lean_box(0);
                    v___x_5103_ = l_instInhabitedOfMonad___redArg(v___x_5099_, v___x_5102_);
                    v___f_5104_ = crate::leanh::lean_alloc_closure(
                        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_5104_, 0, v___x_5103_);
                    v___x_5105_ = (crate::leanh::lean_unbox(v_a_5101_) as u8);
                    match v___x_5105_ {
                        0 => {
                            v___f_5106_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Compiler_LCNF_Decl_save___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                7,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___f_5106_, 0, v_decl_5077_);
                            v___x_5107_ = (crate::leanh::lean_unbox(v_a_5101_) as u8);
                            crate::leanh::lean_dec(v_a_5101_);
                            v___x_380__overap_5108_ =
                                l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(
                                    v___f_5104_,
                                    v___x_5107_,
                                    v_pu_5076_,
                                    v___f_5106_,
                                );
                            crate::leanh::lean_dec_ref(v___f_5104_);
                            crate::leanh::lean_inc(v_a_5081_);
                            crate::leanh::lean_inc_ref(v_a_5080_);
                            crate::leanh::lean_inc(v_a_5079_);
                            crate::leanh::lean_inc_ref(v_a_5078_);
                            v___x_5109_ = crate::leanh::lean_apply_5(
                                v___x_380__overap_5108_,
                                v_a_5078_,
                                v_a_5079_,
                                v_a_5080_,
                                v_a_5081_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_5109_;
                        }
                        1 => {
                            v___f_5110_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Compiler_LCNF_Decl_save___lam__1___boxed
                                    as *mut core::ffi::c_void,
                                7,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___f_5110_, 0, v_decl_5077_);
                            v___x_5111_ = (crate::leanh::lean_unbox(v_a_5101_) as u8);
                            crate::leanh::lean_dec(v_a_5101_);
                            v___x_398__overap_5112_ =
                                l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(
                                    v___f_5104_,
                                    v___x_5111_,
                                    v_pu_5076_,
                                    v___f_5110_,
                                );
                            crate::leanh::lean_dec_ref(v___f_5104_);
                            crate::leanh::lean_inc(v_a_5081_);
                            crate::leanh::lean_inc_ref(v_a_5080_);
                            crate::leanh::lean_inc(v_a_5079_);
                            crate::leanh::lean_inc_ref(v_a_5078_);
                            v___x_5113_ = crate::leanh::lean_apply_5(
                                v___x_398__overap_5112_,
                                v_a_5078_,
                                v_a_5079_,
                                v_a_5080_,
                                v_a_5081_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_5113_;
                        }
                        _ => {
                            v___f_5114_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Compiler_LCNF_Decl_save___lam__2___boxed
                                    as *mut core::ffi::c_void,
                                7,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___f_5114_, 0, v_decl_5077_);
                            v___x_5115_ = (crate::leanh::lean_unbox(v_a_5101_) as u8);
                            crate::leanh::lean_dec(v_a_5101_);
                            v___x_416__overap_5116_ =
                                l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(
                                    v___f_5104_,
                                    v___x_5115_,
                                    v_pu_5076_,
                                    v___f_5114_,
                                );
                            crate::leanh::lean_dec_ref(v___f_5104_);
                            crate::leanh::lean_inc(v_a_5081_);
                            crate::leanh::lean_inc_ref(v_a_5080_);
                            crate::leanh::lean_inc(v_a_5079_);
                            crate::leanh::lean_inc_ref(v_a_5078_);
                            v___x_5117_ = crate::leanh::lean_apply_5(
                                v___x_416__overap_5116_,
                                v_a_5078_,
                                v_a_5079_,
                                v_a_5080_,
                                v_a_5081_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_5117_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5099_);
                    crate::leanh::lean_dec_ref(v_decl_5077_);
                    v_a_5118_ = crate::leanh::lean_ctor_get(v___x_5100_, 0);
                    v_isSharedCheck_5125_ = (!crate::leanh::lean_is_exclusive(v___x_5100_)) as u8;
                    if v_isSharedCheck_5125_ == 0 {
                        v___x_5120_ = v___x_5100_;
                        v_isShared_5121_ = v_isSharedCheck_5125_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5118_);
                        crate::leanh::lean_dec(v___x_5100_);
                        v___x_5120_ = crate::leanh::lean_box(0);
                        v_isShared_5121_ = v_isSharedCheck_5125_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5121_ == 0 {
                    v___x_5123_ = v___x_5120_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5124_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_a_5118_);
                    v___x_5123_ = v_reuseFailAlloc_5124_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5123_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_save___boxed(
    mut v_pu_5126_: *mut crate::leanh::LeanObject,
    mut v_decl_5127_: *mut crate::leanh::LeanObject,
    mut v_a_5128_: *mut crate::leanh::LeanObject,
    mut v_a_5129_: *mut crate::leanh::LeanObject,
    mut v_a_5130_: *mut crate::leanh::LeanObject,
    mut v_a_5131_: *mut crate::leanh::LeanObject,
    mut v_a_5132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5133_: u8 = 0;
    let mut v_res_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5133_ = (crate::leanh::lean_unbox(v_pu_5126_) as u8);
    v_res_5134_ = l_Lean_Compiler_LCNF_Decl_save(
        v_pu_boxed_5133_,
        v_decl_5127_,
        v_a_5128_,
        v_a_5129_,
        v_a_5130_,
        v_a_5131_,
    );
    crate::leanh::lean_dec(v_a_5131_);
    crate::leanh::lean_dec_ref(v_a_5130_);
    crate::leanh::lean_dec(v_a_5129_);
    crate::leanh::lean_dec_ref(v_a_5128_);
    return v_res_5134_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5135_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5135_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5136_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0);
    v___x_5137_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5137_, 0, v___x_5136_);
    return v___x_5137_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5138_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1);
    v___x_5139_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5140_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5140_, 0, v___x_5139_);
    crate::leanh::lean_ctor_set(v___x_5140_, 1, v___x_5139_);
    crate::leanh::lean_ctor_set(v___x_5140_, 2, v___x_5139_);
    crate::leanh::lean_ctor_set(v___x_5140_, 3, v___x_5139_);
    crate::leanh::lean_ctor_set(v___x_5140_, 4, v___x_5138_);
    crate::leanh::lean_ctor_set(v___x_5140_, 5, v___x_5138_);
    crate::leanh::lean_ctor_set(v___x_5140_, 6, v___x_5138_);
    crate::leanh::lean_ctor_set(v___x_5140_, 7, v___x_5138_);
    crate::leanh::lean_ctor_set(v___x_5140_, 8, v___x_5138_);
    crate::leanh::lean_ctor_set(v___x_5140_, 9, v___x_5138_);
    return v___x_5140_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5141_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5142_ = lean_mk_empty_array_with_capacity(v___x_5141_);
    v___x_5143_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5143_, 0, v___x_5142_);
    return v___x_5143_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5144_: usize = 0;
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5144_ = 5usize;
    v___x_5145_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5146_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5147_ = lean_mk_empty_array_with_capacity(v___x_5146_);
    v___x_5148_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3);
    v___x_5149_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_5149_, 0, v___x_5148_);
    crate::leanh::lean_ctor_set(v___x_5149_, 1, v___x_5147_);
    crate::leanh::lean_ctor_set(v___x_5149_, 2, v___x_5145_);
    crate::leanh::lean_ctor_set(v___x_5149_, 3, v___x_5145_);
    crate::leanh::lean_ctor_set_usize(v___x_5149_, 4, v___x_5144_);
    return v___x_5149_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5150_ = crate::leanh::lean_box(1);
    v___x_5151_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4);
    v___x_5152_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1);
    v___x_5153_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5153_, 0, v___x_5152_);
    crate::leanh::lean_ctor_set(v___x_5153_, 1, v___x_5151_);
    crate::leanh::lean_ctor_set(v___x_5153_, 2, v___x_5150_);
    return v___x_5153_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0(
    mut v_msgData_5154_: *mut crate::leanh::LeanObject,
    mut v___y_5155_: *mut crate::leanh::LeanObject,
    mut v___y_5156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5158_ = lean_st_ref_get(v___y_5156_);
    v_env_5159_ = crate::leanh::lean_ctor_get(v___x_5158_, 0);
    crate::leanh::lean_inc_ref(v_env_5159_);
    crate::leanh::lean_dec(v___x_5158_);
    v_options_5160_ = crate::leanh::lean_ctor_get(v___y_5155_, 2);
    v___x_5161_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2);
    v___x_5162_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5);
    crate::leanh::lean_inc_ref(v_options_5160_);
    v___x_5163_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5163_, 0, v_env_5159_);
    crate::leanh::lean_ctor_set(v___x_5163_, 1, v___x_5161_);
    crate::leanh::lean_ctor_set(v___x_5163_, 2, v___x_5162_);
    crate::leanh::lean_ctor_set(v___x_5163_, 3, v_options_5160_);
    v___x_5164_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5164_, 0, v___x_5163_);
    crate::leanh::lean_ctor_set(v___x_5164_, 1, v_msgData_5154_);
    v___x_5165_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5165_, 0, v___x_5164_);
    return v___x_5165_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___boxed(
    mut v_msgData_5166_: *mut crate::leanh::LeanObject,
    mut v___y_5167_: *mut crate::leanh::LeanObject,
    mut v___y_5168_: *mut crate::leanh::LeanObject,
    mut v___y_5169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5170_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0(v_msgData_5166_, v___y_5167_, v___y_5168_);
    crate::leanh::lean_dec(v___y_5168_);
    crate::leanh::lean_dec_ref(v___y_5167_);
    return v_res_5170_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(
    mut v_msg_5171_: *mut crate::leanh::LeanObject,
    mut v___y_5172_: *mut crate::leanh::LeanObject,
    mut v___y_5173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5180_: u8 = 0;
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5185_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5175_ = crate::leanh::lean_ctor_get(v___y_5172_, 5);
                v___x_5176_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0(v_msg_5171_, v___y_5172_, v___y_5173_);
                v_a_5177_ = crate::leanh::lean_ctor_get(v___x_5176_, 0);
                v_isSharedCheck_5185_ = (!crate::leanh::lean_is_exclusive(v___x_5176_)) as u8;
                if v_isSharedCheck_5185_ == 0 {
                    v___x_5179_ = v___x_5176_;
                    v_isShared_5180_ = v_isSharedCheck_5185_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5177_);
                    crate::leanh::lean_dec(v___x_5176_);
                    v___x_5179_ = crate::leanh::lean_box(0);
                    v_isShared_5180_ = v_isSharedCheck_5185_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_5175_);
                v___x_5181_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5181_, 0, v_ref_5175_);
                crate::leanh::lean_ctor_set(v___x_5181_, 1, v_a_5177_);
                if v_isShared_5180_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5179_, 1);
                    crate::leanh::lean_ctor_set(v___x_5179_, 0, v___x_5181_);
                    v___x_5183_ = v___x_5179_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5184_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5184_, 0, v___x_5181_);
                    v___x_5183_ = v_reuseFailAlloc_5184_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5183_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg___boxed(
    mut v_msg_5186_: *mut crate::leanh::LeanObject,
    mut v___y_5187_: *mut crate::leanh::LeanObject,
    mut v___y_5188_: *mut crate::leanh::LeanObject,
    mut v___y_5189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5190_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(
        v_msg_5186_,
        v___y_5187_,
        v___y_5188_,
    );
    crate::leanh::lean_dec(v___y_5188_);
    crate::leanh::lean_dec_ref(v___y_5187_);
    return v_res_5190_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5192_ = l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__0;
    v___x_5193_ = l_Lean_stringToMessageData(v___x_5192_);
    return v___x_5193_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getDeclAt_x3f(
    mut v_declName_5194_: *mut crate::leanh::LeanObject,
    mut v_phase_5195_: u8,
    mut v_a_5196_: *mut crate::leanh::LeanObject,
    mut v_a_5197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_phase_5195_ {
        0 => {
            let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5199_ =
                l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(v_declName_5194_, v_a_5197_);
            return v___x_5199_;
        }
        1 => {
            let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5200_ =
                l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_5194_, v_a_5197_);
            return v___x_5200_;
        }
        _ => {
            let mut v___x_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_declName_5194_);
            v___x_5201_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1),
                core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1_once),
                _init_l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1,
            );
            v___x_5202_ =
                l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(
                    v___x_5201_,
                    v_a_5196_,
                    v_a_5197_,
                );
            return v___x_5202_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getDeclAt_x3f___boxed(
    mut v_declName_5203_: *mut crate::leanh::LeanObject,
    mut v_phase_5204_: *mut crate::leanh::LeanObject,
    mut v_a_5205_: *mut crate::leanh::LeanObject,
    mut v_a_5206_: *mut crate::leanh::LeanObject,
    mut v_a_5207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_5208_: u8 = 0;
    let mut v_res_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_5208_ = (crate::leanh::lean_unbox(v_phase_5204_) as u8);
    v_res_5209_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(
        v_declName_5203_,
        v_phase_boxed_5208_,
        v_a_5205_,
        v_a_5206_,
    );
    crate::leanh::lean_dec(v_a_5206_);
    crate::leanh::lean_dec_ref(v_a_5205_);
    return v_res_5209_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0(
    mut v_00_u03b1_5210_: *mut crate::leanh::LeanObject,
    mut v_msg_5211_: *mut crate::leanh::LeanObject,
    mut v___y_5212_: *mut crate::leanh::LeanObject,
    mut v___y_5213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5215_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(
        v_msg_5211_,
        v___y_5212_,
        v___y_5213_,
    );
    return v___x_5215_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___boxed(
    mut v_00_u03b1_5216_: *mut crate::leanh::LeanObject,
    mut v_msg_5217_: *mut crate::leanh::LeanObject,
    mut v___y_5218_: *mut crate::leanh::LeanObject,
    mut v___y_5219_: *mut crate::leanh::LeanObject,
    mut v___y_5220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5221_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0(
        v_00_u03b1_5216_,
        v_msg_5217_,
        v___y_5218_,
        v___y_5219_,
    );
    crate::leanh::lean_dec(v___y_5219_);
    crate::leanh::lean_dec_ref(v___y_5218_);
    return v_res_5221_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getDecl_x3f___redArg(
    mut v_declName_5222_: *mut crate::leanh::LeanObject,
    mut v_a_5223_: *mut crate::leanh::LeanObject,
    mut v_a_5224_: *mut crate::leanh::LeanObject,
    mut v_a_5225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: u8 = 0;
    let mut v___x_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5234_: u8 = 0;
    let mut v_val_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5238_: u8 = 0;
    let mut v___x_5239_: u8 = 0;
    let mut v___x_5240_: u8 = 0;
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5249_: u8 = 0;
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5254_: u8 = 0;
    let mut v_a_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5258_: u8 = 0;
    let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5262_: u8 = 0;
    let mut v_a_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5266_: u8 = 0;
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5270_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5227_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_5223_);
                if crate::leanh::lean_obj_tag(v___x_5227_) == 0 {
                    v_a_5228_ = crate::leanh::lean_ctor_get(v___x_5227_, 0);
                    crate::leanh::lean_inc(v_a_5228_);
                    crate::leanh::lean_dec_ref_known(v___x_5227_, 1);
                    v___x_5229_ = (crate::leanh::lean_unbox(v_a_5228_) as u8);
                    v___x_5230_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(
                        v_declName_5222_,
                        v___x_5229_,
                        v_a_5224_,
                        v_a_5225_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5230_) == 0 {
                        v_a_5231_ = crate::leanh::lean_ctor_get(v___x_5230_, 0);
                        v_isSharedCheck_5254_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5230_)) as u8;
                        if v_isSharedCheck_5254_ == 0 {
                            v___x_5233_ = v___x_5230_;
                            v_isShared_5234_ = v_isSharedCheck_5254_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5231_);
                            crate::leanh::lean_dec(v___x_5230_);
                            v___x_5233_ = crate::leanh::lean_box(0);
                            v_isShared_5234_ = v_isSharedCheck_5254_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5228_);
                        v_a_5255_ = crate::leanh::lean_ctor_get(v___x_5230_, 0);
                        v_isSharedCheck_5262_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5230_)) as u8;
                        if v_isSharedCheck_5262_ == 0 {
                            v___x_5257_ = v___x_5230_;
                            v_isShared_5258_ = v_isSharedCheck_5262_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5255_);
                            crate::leanh::lean_dec(v___x_5230_);
                            v___x_5257_ = crate::leanh::lean_box(0);
                            v_isShared_5258_ = v_isSharedCheck_5262_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_5222_);
                    v_a_5263_ = crate::leanh::lean_ctor_get(v___x_5227_, 0);
                    v_isSharedCheck_5270_ = (!crate::leanh::lean_is_exclusive(v___x_5227_)) as u8;
                    if v_isSharedCheck_5270_ == 0 {
                        v___x_5265_ = v___x_5227_;
                        v_isShared_5266_ = v_isSharedCheck_5270_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5263_);
                        crate::leanh::lean_dec(v___x_5227_);
                        v___x_5265_ = crate::leanh::lean_box(0);
                        v_isShared_5266_ = v_isSharedCheck_5270_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5231_) == 1 {
                    v_val_5235_ = crate::leanh::lean_ctor_get(v_a_5231_, 0);
                    v_isSharedCheck_5249_ = (!crate::leanh::lean_is_exclusive(v_a_5231_)) as u8;
                    if v_isSharedCheck_5249_ == 0 {
                        v___x_5237_ = v_a_5231_;
                        v_isShared_5238_ = v_isSharedCheck_5249_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5235_);
                        crate::leanh::lean_dec(v_a_5231_);
                        v___x_5237_ = crate::leanh::lean_box(0);
                        v_isShared_5238_ = v_isSharedCheck_5249_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5231_);
                    crate::leanh::lean_dec(v_a_5228_);
                    v___x_5250_ = crate::leanh::lean_box(0);
                    if v_isShared_5234_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5233_, 0, v___x_5250_);
                        v___x_5252_ = v___x_5233_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5253_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5253_, 0, v___x_5250_);
                        v___x_5252_ = v_reuseFailAlloc_5253_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5239_ = (crate::leanh::lean_unbox(v_a_5228_) as u8);
                crate::leanh::lean_dec(v_a_5228_);
                v___x_5240_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_5239_);
                v___x_5241_ = crate::leanh::lean_box((v___x_5240_) as usize);
                v___x_5242_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5242_, 0, v___x_5241_);
                crate::leanh::lean_ctor_set(v___x_5242_, 1, v_val_5235_);
                if v_isShared_5238_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5237_, 0, v___x_5242_);
                    v___x_5244_ = v___x_5237_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5248_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5248_, 0, v___x_5242_);
                    v___x_5244_ = v_reuseFailAlloc_5248_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5234_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5233_, 0, v___x_5244_);
                    v___x_5246_ = v___x_5233_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5247_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5247_, 0, v___x_5244_);
                    v___x_5246_ = v_reuseFailAlloc_5247_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5246_;
            }
            5 => {
                return v___x_5252_;
            }
            6 => {
                if v_isShared_5258_ == 0 {
                    v___x_5260_ = v___x_5257_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5261_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_a_5255_);
                    v___x_5260_ = v_reuseFailAlloc_5261_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5260_;
            }
            8 => {
                if v_isShared_5266_ == 0 {
                    v___x_5268_ = v___x_5265_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5269_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5269_, 0, v_a_5263_);
                    v___x_5268_ = v_reuseFailAlloc_5269_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5268_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getDecl_x3f___redArg___boxed(
    mut v_declName_5271_: *mut crate::leanh::LeanObject,
    mut v_a_5272_: *mut crate::leanh::LeanObject,
    mut v_a_5273_: *mut crate::leanh::LeanObject,
    mut v_a_5274_: *mut crate::leanh::LeanObject,
    mut v_a_5275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5276_ = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(
        v_declName_5271_,
        v_a_5272_,
        v_a_5273_,
        v_a_5274_,
    );
    crate::leanh::lean_dec(v_a_5274_);
    crate::leanh::lean_dec_ref(v_a_5273_);
    crate::leanh::lean_dec_ref(v_a_5272_);
    return v_res_5276_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getDecl_x3f(
    mut v_declName_5277_: *mut crate::leanh::LeanObject,
    mut v_a_5278_: *mut crate::leanh::LeanObject,
    mut v_a_5279_: *mut crate::leanh::LeanObject,
    mut v_a_5280_: *mut crate::leanh::LeanObject,
    mut v_a_5281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: u8 = 0;
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5290_: u8 = 0;
    let mut v_val_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5294_: u8 = 0;
    let mut v___x_5295_: u8 = 0;
    let mut v___x_5296_: u8 = 0;
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5305_: u8 = 0;
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5310_: u8 = 0;
    let mut v_a_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5314_: u8 = 0;
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5318_: u8 = 0;
    let mut v_a_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5322_: u8 = 0;
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5326_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5283_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_5278_);
                if crate::leanh::lean_obj_tag(v___x_5283_) == 0 {
                    v_a_5284_ = crate::leanh::lean_ctor_get(v___x_5283_, 0);
                    crate::leanh::lean_inc(v_a_5284_);
                    crate::leanh::lean_dec_ref_known(v___x_5283_, 1);
                    v___x_5285_ = (crate::leanh::lean_unbox(v_a_5284_) as u8);
                    v___x_5286_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(
                        v_declName_5277_,
                        v___x_5285_,
                        v_a_5280_,
                        v_a_5281_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5286_) == 0 {
                        v_a_5287_ = crate::leanh::lean_ctor_get(v___x_5286_, 0);
                        v_isSharedCheck_5310_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5286_)) as u8;
                        if v_isSharedCheck_5310_ == 0 {
                            v___x_5289_ = v___x_5286_;
                            v_isShared_5290_ = v_isSharedCheck_5310_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5287_);
                            crate::leanh::lean_dec(v___x_5286_);
                            v___x_5289_ = crate::leanh::lean_box(0);
                            v_isShared_5290_ = v_isSharedCheck_5310_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5284_);
                        v_a_5311_ = crate::leanh::lean_ctor_get(v___x_5286_, 0);
                        v_isSharedCheck_5318_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5286_)) as u8;
                        if v_isSharedCheck_5318_ == 0 {
                            v___x_5313_ = v___x_5286_;
                            v_isShared_5314_ = v_isSharedCheck_5318_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5311_);
                            crate::leanh::lean_dec(v___x_5286_);
                            v___x_5313_ = crate::leanh::lean_box(0);
                            v_isShared_5314_ = v_isSharedCheck_5318_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_5277_);
                    v_a_5319_ = crate::leanh::lean_ctor_get(v___x_5283_, 0);
                    v_isSharedCheck_5326_ = (!crate::leanh::lean_is_exclusive(v___x_5283_)) as u8;
                    if v_isSharedCheck_5326_ == 0 {
                        v___x_5321_ = v___x_5283_;
                        v_isShared_5322_ = v_isSharedCheck_5326_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5319_);
                        crate::leanh::lean_dec(v___x_5283_);
                        v___x_5321_ = crate::leanh::lean_box(0);
                        v_isShared_5322_ = v_isSharedCheck_5326_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5287_) == 1 {
                    v_val_5291_ = crate::leanh::lean_ctor_get(v_a_5287_, 0);
                    v_isSharedCheck_5305_ = (!crate::leanh::lean_is_exclusive(v_a_5287_)) as u8;
                    if v_isSharedCheck_5305_ == 0 {
                        v___x_5293_ = v_a_5287_;
                        v_isShared_5294_ = v_isSharedCheck_5305_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5291_);
                        crate::leanh::lean_dec(v_a_5287_);
                        v___x_5293_ = crate::leanh::lean_box(0);
                        v_isShared_5294_ = v_isSharedCheck_5305_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5287_);
                    crate::leanh::lean_dec(v_a_5284_);
                    v___x_5306_ = crate::leanh::lean_box(0);
                    if v_isShared_5290_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5289_, 0, v___x_5306_);
                        v___x_5308_ = v___x_5289_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5309_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5309_, 0, v___x_5306_);
                        v___x_5308_ = v_reuseFailAlloc_5309_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5295_ = (crate::leanh::lean_unbox(v_a_5284_) as u8);
                crate::leanh::lean_dec(v_a_5284_);
                v___x_5296_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_5295_);
                v___x_5297_ = crate::leanh::lean_box((v___x_5296_) as usize);
                v___x_5298_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5298_, 0, v___x_5297_);
                crate::leanh::lean_ctor_set(v___x_5298_, 1, v_val_5291_);
                if v_isShared_5294_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5293_, 0, v___x_5298_);
                    v___x_5300_ = v___x_5293_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5304_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 0, v___x_5298_);
                    v___x_5300_ = v_reuseFailAlloc_5304_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5289_, 0, v___x_5300_);
                    v___x_5302_ = v___x_5289_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5303_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5303_, 0, v___x_5300_);
                    v___x_5302_ = v_reuseFailAlloc_5303_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5302_;
            }
            5 => {
                return v___x_5308_;
            }
            6 => {
                if v_isShared_5314_ == 0 {
                    v___x_5316_ = v___x_5313_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5317_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5317_, 0, v_a_5311_);
                    v___x_5316_ = v_reuseFailAlloc_5317_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5316_;
            }
            8 => {
                if v_isShared_5322_ == 0 {
                    v___x_5324_ = v___x_5321_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5325_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_a_5319_);
                    v___x_5324_ = v_reuseFailAlloc_5325_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5324_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getDecl_x3f___boxed(
    mut v_declName_5327_: *mut crate::leanh::LeanObject,
    mut v_a_5328_: *mut crate::leanh::LeanObject,
    mut v_a_5329_: *mut crate::leanh::LeanObject,
    mut v_a_5330_: *mut crate::leanh::LeanObject,
    mut v_a_5331_: *mut crate::leanh::LeanObject,
    mut v_a_5332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5333_ = l_Lean_Compiler_LCNF_getDecl_x3f(
        v_declName_5327_,
        v_a_5328_,
        v_a_5329_,
        v_a_5330_,
        v_a_5331_,
    );
    crate::leanh::lean_dec(v_a_5331_);
    crate::leanh::lean_dec_ref(v_a_5330_);
    crate::leanh::lean_dec(v_a_5329_);
    crate::leanh::lean_dec_ref(v_a_5328_);
    return v_res_5333_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(
    mut v_declName_5334_: *mut crate::leanh::LeanObject,
    mut v_phase_5335_: u8,
    mut v_a_5336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5338_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2_once),
        _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2,
    );
    match v_phase_5335_ {
        0 => {
            let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_env_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toEnvExtension_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_asyncMode_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5339_ = lean_st_ref_get(v_a_5336_);
            v_env_5340_ = crate::leanh::lean_ctor_get(v___x_5339_, 0);
            crate::leanh::lean_inc_ref(v_env_5340_);
            crate::leanh::lean_dec(v___x_5339_);
            v___x_5341_ = l_Lean_Compiler_LCNF_baseExt;
            v_toEnvExtension_5342_ = crate::leanh::lean_ctor_get(v___x_5341_, 0);
            v_asyncMode_5343_ = crate::leanh::lean_ctor_get(v_toEnvExtension_5342_, 2);
            v___x_5344_ = crate::leanh::lean_box(0);
            v___x_5345_ = l_Lean_PersistentEnvExtension_getState___redArg(
                v___x_5338_,
                v___x_5341_,
                v_env_5340_,
                v_asyncMode_5343_,
                v___x_5344_,
            );
            v___x_5346_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_5345_, v_declName_5334_);
            crate::leanh::lean_dec(v___x_5345_);
            v___x_5347_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5347_, 0, v___x_5346_);
            return v___x_5347_;
        }
        1 => {
            let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_env_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toEnvExtension_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_asyncMode_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5348_ = lean_st_ref_get(v_a_5336_);
            v_env_5349_ = crate::leanh::lean_ctor_get(v___x_5348_, 0);
            crate::leanh::lean_inc_ref(v_env_5349_);
            crate::leanh::lean_dec(v___x_5348_);
            v___x_5350_ = l_Lean_Compiler_LCNF_monoExt;
            v_toEnvExtension_5351_ = crate::leanh::lean_ctor_get(v___x_5350_, 0);
            v_asyncMode_5352_ = crate::leanh::lean_ctor_get(v_toEnvExtension_5351_, 2);
            v___x_5353_ = crate::leanh::lean_box(0);
            v___x_5354_ = l_Lean_PersistentEnvExtension_getState___redArg(
                v___x_5338_,
                v___x_5350_,
                v_env_5349_,
                v_asyncMode_5352_,
                v___x_5353_,
            );
            v___x_5355_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_5354_, v_declName_5334_);
            crate::leanh::lean_dec(v___x_5354_);
            v___x_5356_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5356_, 0, v___x_5355_);
            return v___x_5356_;
        }
        _ => {
            let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_env_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_asyncMode_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5357_ = lean_st_ref_get(v_a_5336_);
            v_env_5358_ = crate::leanh::lean_ctor_get(v___x_5357_, 0);
            crate::leanh::lean_inc_ref(v_env_5358_);
            crate::leanh::lean_dec(v___x_5357_);
            v___x_5359_ = l_Lean_Compiler_LCNF_impureExt;
            v_asyncMode_5360_ = crate::leanh::lean_ctor_get(v___x_5359_, 2);
            v___x_5361_ = crate::leanh::lean_box(0);
            v___x_5362_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                v___x_5338_,
                v___x_5359_,
                v_env_5358_,
                v_asyncMode_5360_,
                v___x_5361_,
            );
            v___x_5363_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_5362_, v_declName_5334_);
            crate::leanh::lean_dec(v___x_5362_);
            v___x_5364_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5364_, 0, v___x_5363_);
            return v___x_5364_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg___boxed(
    mut v_declName_5365_: *mut crate::leanh::LeanObject,
    mut v_phase_5366_: *mut crate::leanh::LeanObject,
    mut v_a_5367_: *mut crate::leanh::LeanObject,
    mut v_a_5368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_5369_: u8 = 0;
    let mut v_res_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_5369_ = (crate::leanh::lean_unbox(v_phase_5366_) as u8);
    v_res_5370_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(
        v_declName_5365_,
        v_phase_boxed_5369_,
        v_a_5367_,
    );
    crate::leanh::lean_dec(v_a_5367_);
    crate::leanh::lean_dec(v_declName_5365_);
    return v_res_5370_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getLocalDeclAt_x3f(
    mut v_declName_5371_: *mut crate::leanh::LeanObject,
    mut v_phase_5372_: u8,
    mut v_a_5373_: *mut crate::leanh::LeanObject,
    mut v_a_5374_: *mut crate::leanh::LeanObject,
    mut v_a_5375_: *mut crate::leanh::LeanObject,
    mut v_a_5376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5378_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(
        v_declName_5371_,
        v_phase_5372_,
        v_a_5376_,
    );
    return v___x_5378_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___boxed(
    mut v_declName_5379_: *mut crate::leanh::LeanObject,
    mut v_phase_5380_: *mut crate::leanh::LeanObject,
    mut v_a_5381_: *mut crate::leanh::LeanObject,
    mut v_a_5382_: *mut crate::leanh::LeanObject,
    mut v_a_5383_: *mut crate::leanh::LeanObject,
    mut v_a_5384_: *mut crate::leanh::LeanObject,
    mut v_a_5385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_5386_: u8 = 0;
    let mut v_res_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_5386_ = (crate::leanh::lean_unbox(v_phase_5380_) as u8);
    v_res_5387_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f(
        v_declName_5379_,
        v_phase_boxed_5386_,
        v_a_5381_,
        v_a_5382_,
        v_a_5383_,
        v_a_5384_,
    );
    crate::leanh::lean_dec(v_a_5384_);
    crate::leanh::lean_dec_ref(v_a_5383_);
    crate::leanh::lean_dec(v_a_5382_);
    crate::leanh::lean_dec_ref(v_a_5381_);
    crate::leanh::lean_dec(v_declName_5379_);
    return v_res_5387_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getLocalDecl_x3f___redArg(
    mut v_declName_5388_: *mut crate::leanh::LeanObject,
    mut v_a_5389_: *mut crate::leanh::LeanObject,
    mut v_a_5390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: u8 = 0;
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5399_: u8 = 0;
    let mut v_val_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5403_: u8 = 0;
    let mut v___x_5404_: u8 = 0;
    let mut v___x_5405_: u8 = 0;
    let mut v___x_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5414_: u8 = 0;
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5419_: u8 = 0;
    let mut v_a_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5423_: u8 = 0;
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5392_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_5389_);
                if crate::leanh::lean_obj_tag(v___x_5392_) == 0 {
                    v_a_5393_ = crate::leanh::lean_ctor_get(v___x_5392_, 0);
                    crate::leanh::lean_inc(v_a_5393_);
                    crate::leanh::lean_dec_ref_known(v___x_5392_, 1);
                    v___x_5394_ = (crate::leanh::lean_unbox(v_a_5393_) as u8);
                    v___x_5395_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(
                        v_declName_5388_,
                        v___x_5394_,
                        v_a_5390_,
                    );
                    v_a_5396_ = crate::leanh::lean_ctor_get(v___x_5395_, 0);
                    v_isSharedCheck_5419_ = (!crate::leanh::lean_is_exclusive(v___x_5395_)) as u8;
                    if v_isSharedCheck_5419_ == 0 {
                        v___x_5398_ = v___x_5395_;
                        v_isShared_5399_ = v_isSharedCheck_5419_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5396_);
                        crate::leanh::lean_dec(v___x_5395_);
                        v___x_5398_ = crate::leanh::lean_box(0);
                        v_isShared_5399_ = v_isSharedCheck_5419_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5420_ = crate::leanh::lean_ctor_get(v___x_5392_, 0);
                    v_isSharedCheck_5427_ = (!crate::leanh::lean_is_exclusive(v___x_5392_)) as u8;
                    if v_isSharedCheck_5427_ == 0 {
                        v___x_5422_ = v___x_5392_;
                        v_isShared_5423_ = v_isSharedCheck_5427_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5420_);
                        crate::leanh::lean_dec(v___x_5392_);
                        v___x_5422_ = crate::leanh::lean_box(0);
                        v_isShared_5423_ = v_isSharedCheck_5427_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5396_) == 1 {
                    v_val_5400_ = crate::leanh::lean_ctor_get(v_a_5396_, 0);
                    v_isSharedCheck_5414_ = (!crate::leanh::lean_is_exclusive(v_a_5396_)) as u8;
                    if v_isSharedCheck_5414_ == 0 {
                        v___x_5402_ = v_a_5396_;
                        v_isShared_5403_ = v_isSharedCheck_5414_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5400_);
                        crate::leanh::lean_dec(v_a_5396_);
                        v___x_5402_ = crate::leanh::lean_box(0);
                        v_isShared_5403_ = v_isSharedCheck_5414_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5396_);
                    crate::leanh::lean_dec(v_a_5393_);
                    v___x_5415_ = crate::leanh::lean_box(0);
                    if v_isShared_5399_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5398_, 0, v___x_5415_);
                        v___x_5417_ = v___x_5398_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5418_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5418_, 0, v___x_5415_);
                        v___x_5417_ = v_reuseFailAlloc_5418_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5404_ = (crate::leanh::lean_unbox(v_a_5393_) as u8);
                crate::leanh::lean_dec(v_a_5393_);
                v___x_5405_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_5404_);
                v___x_5406_ = crate::leanh::lean_box((v___x_5405_) as usize);
                v___x_5407_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5407_, 0, v___x_5406_);
                crate::leanh::lean_ctor_set(v___x_5407_, 1, v_val_5400_);
                if v_isShared_5403_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5402_, 0, v___x_5407_);
                    v___x_5409_ = v___x_5402_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5413_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5413_, 0, v___x_5407_);
                    v___x_5409_ = v_reuseFailAlloc_5413_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5399_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5398_, 0, v___x_5409_);
                    v___x_5411_ = v___x_5398_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5412_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 0, v___x_5409_);
                    v___x_5411_ = v_reuseFailAlloc_5412_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5411_;
            }
            5 => {
                return v___x_5417_;
            }
            6 => {
                if v_isShared_5423_ == 0 {
                    v___x_5425_ = v___x_5422_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5426_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5426_, 0, v_a_5420_);
                    v___x_5425_ = v_reuseFailAlloc_5426_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5425_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getLocalDecl_x3f___redArg___boxed(
    mut v_declName_5428_: *mut crate::leanh::LeanObject,
    mut v_a_5429_: *mut crate::leanh::LeanObject,
    mut v_a_5430_: *mut crate::leanh::LeanObject,
    mut v_a_5431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5432_ =
        l_Lean_Compiler_LCNF_getLocalDecl_x3f___redArg(v_declName_5428_, v_a_5429_, v_a_5430_);
    crate::leanh::lean_dec(v_a_5430_);
    crate::leanh::lean_dec_ref(v_a_5429_);
    crate::leanh::lean_dec(v_declName_5428_);
    return v_res_5432_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getLocalDecl_x3f(
    mut v_declName_5433_: *mut crate::leanh::LeanObject,
    mut v_a_5434_: *mut crate::leanh::LeanObject,
    mut v_a_5435_: *mut crate::leanh::LeanObject,
    mut v_a_5436_: *mut crate::leanh::LeanObject,
    mut v_a_5437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: u8 = 0;
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5446_: u8 = 0;
    let mut v_val_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5450_: u8 = 0;
    let mut v___x_5451_: u8 = 0;
    let mut v___x_5452_: u8 = 0;
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5461_: u8 = 0;
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5466_: u8 = 0;
    let mut v_a_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5470_: u8 = 0;
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5474_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5439_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_5434_);
                if crate::leanh::lean_obj_tag(v___x_5439_) == 0 {
                    v_a_5440_ = crate::leanh::lean_ctor_get(v___x_5439_, 0);
                    crate::leanh::lean_inc(v_a_5440_);
                    crate::leanh::lean_dec_ref_known(v___x_5439_, 1);
                    v___x_5441_ = (crate::leanh::lean_unbox(v_a_5440_) as u8);
                    v___x_5442_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(
                        v_declName_5433_,
                        v___x_5441_,
                        v_a_5437_,
                    );
                    v_a_5443_ = crate::leanh::lean_ctor_get(v___x_5442_, 0);
                    v_isSharedCheck_5466_ = (!crate::leanh::lean_is_exclusive(v___x_5442_)) as u8;
                    if v_isSharedCheck_5466_ == 0 {
                        v___x_5445_ = v___x_5442_;
                        v_isShared_5446_ = v_isSharedCheck_5466_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5443_);
                        crate::leanh::lean_dec(v___x_5442_);
                        v___x_5445_ = crate::leanh::lean_box(0);
                        v_isShared_5446_ = v_isSharedCheck_5466_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5467_ = crate::leanh::lean_ctor_get(v___x_5439_, 0);
                    v_isSharedCheck_5474_ = (!crate::leanh::lean_is_exclusive(v___x_5439_)) as u8;
                    if v_isSharedCheck_5474_ == 0 {
                        v___x_5469_ = v___x_5439_;
                        v_isShared_5470_ = v_isSharedCheck_5474_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5467_);
                        crate::leanh::lean_dec(v___x_5439_);
                        v___x_5469_ = crate::leanh::lean_box(0);
                        v_isShared_5470_ = v_isSharedCheck_5474_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5443_) == 1 {
                    v_val_5447_ = crate::leanh::lean_ctor_get(v_a_5443_, 0);
                    v_isSharedCheck_5461_ = (!crate::leanh::lean_is_exclusive(v_a_5443_)) as u8;
                    if v_isSharedCheck_5461_ == 0 {
                        v___x_5449_ = v_a_5443_;
                        v_isShared_5450_ = v_isSharedCheck_5461_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5447_);
                        crate::leanh::lean_dec(v_a_5443_);
                        v___x_5449_ = crate::leanh::lean_box(0);
                        v_isShared_5450_ = v_isSharedCheck_5461_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5443_);
                    crate::leanh::lean_dec(v_a_5440_);
                    v___x_5462_ = crate::leanh::lean_box(0);
                    if v_isShared_5446_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5445_, 0, v___x_5462_);
                        v___x_5464_ = v___x_5445_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5465_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5465_, 0, v___x_5462_);
                        v___x_5464_ = v_reuseFailAlloc_5465_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5451_ = (crate::leanh::lean_unbox(v_a_5440_) as u8);
                crate::leanh::lean_dec(v_a_5440_);
                v___x_5452_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_5451_);
                v___x_5453_ = crate::leanh::lean_box((v___x_5452_) as usize);
                v___x_5454_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5454_, 0, v___x_5453_);
                crate::leanh::lean_ctor_set(v___x_5454_, 1, v_val_5447_);
                if v_isShared_5450_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5449_, 0, v___x_5454_);
                    v___x_5456_ = v___x_5449_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5460_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5460_, 0, v___x_5454_);
                    v___x_5456_ = v_reuseFailAlloc_5460_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5446_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5445_, 0, v___x_5456_);
                    v___x_5458_ = v___x_5445_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5459_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5459_, 0, v___x_5456_);
                    v___x_5458_ = v_reuseFailAlloc_5459_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5458_;
            }
            5 => {
                return v___x_5464_;
            }
            6 => {
                if v_isShared_5470_ == 0 {
                    v___x_5472_ = v___x_5469_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5473_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5473_, 0, v_a_5467_);
                    v___x_5472_ = v_reuseFailAlloc_5473_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getLocalDecl_x3f___boxed(
    mut v_declName_5475_: *mut crate::leanh::LeanObject,
    mut v_a_5476_: *mut crate::leanh::LeanObject,
    mut v_a_5477_: *mut crate::leanh::LeanObject,
    mut v_a_5478_: *mut crate::leanh::LeanObject,
    mut v_a_5479_: *mut crate::leanh::LeanObject,
    mut v_a_5480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5481_ = l_Lean_Compiler_LCNF_getLocalDecl_x3f(
        v_declName_5475_,
        v_a_5476_,
        v_a_5477_,
        v_a_5478_,
        v_a_5479_,
    );
    crate::leanh::lean_dec(v_a_5479_);
    crate::leanh::lean_dec_ref(v_a_5478_);
    crate::leanh::lean_dec(v_a_5477_);
    crate::leanh::lean_dec_ref(v_a_5476_);
    crate::leanh::lean_dec(v_declName_5475_);
    return v_res_5481_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5483_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
    return v___x_5483_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2____boxed(
    mut v_a_5484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5485_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2_();
    return v_res_5485_;
}
pub unsafe fn l_Lean_Compiler_LCNF_recordFinalImpureDecl___lam__0(
    mut v_name_5486_: *mut crate::leanh::LeanObject,
    mut v_s_5487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5492_: u8 = 0;
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5498_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5488_ = crate::leanh::lean_ctor_get(v_s_5487_, 0);
                v_snd_5489_ = crate::leanh::lean_ctor_get(v_s_5487_, 1);
                v_isSharedCheck_5498_ = (!crate::leanh::lean_is_exclusive(v_s_5487_)) as u8;
                if v_isSharedCheck_5498_ == 0 {
                    v___x_5491_ = v_s_5487_;
                    v_isShared_5492_ = v_isSharedCheck_5498_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5489_);
                    crate::leanh::lean_inc(v_fst_5488_);
                    crate::leanh::lean_dec(v_s_5487_);
                    v___x_5491_ = crate::leanh::lean_box(0);
                    v_isShared_5492_ = v_isSharedCheck_5498_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_name_5486_);
                v___x_5493_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5493_, 0, v_name_5486_);
                crate::leanh::lean_ctor_set(v___x_5493_, 1, v_fst_5488_);
                v___x_5494_ = l_Lean_NameSet_insert(v_snd_5489_, v_name_5486_);
                if v_isShared_5492_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5491_, 1, v___x_5494_);
                    crate::leanh::lean_ctor_set(v___x_5491_, 0, v___x_5493_);
                    v___x_5496_ = v___x_5491_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5497_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5497_, 0, v___x_5493_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5497_, 1, v___x_5494_);
                    v___x_5496_ = v_reuseFailAlloc_5497_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5496_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_recordFinalImpureDecl(
    mut v_env_5499_: *mut crate::leanh::LeanObject,
    mut v_name_5500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5501_ = l_Lean_Compiler_LCNF_declOrderExt;
    v_asyncMode_5502_ = crate::leanh::lean_ctor_get(v___x_5501_, 2);
    v___f_5503_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_recordFinalImpureDecl___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5503_, 0, v_name_5500_);
    v___x_5504_ = crate::leanh::lean_box(0);
    v___x_5505_ = l_Lean_EnvExtension_modifyState___redArg(
        v___x_5501_,
        v_env_5499_,
        v___f_5503_,
        v_asyncMode_5502_,
        v___x_5504_,
    );
    return v___x_5505_;
}
pub unsafe fn _init_l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5513_ = l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__1;
    v___x_5514_ = l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__0;
    v___x_5515_ = l_Std_HashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5514_,
        v___x_5513_,
    );
    return v___x_5515_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1(
    mut v_msg_5516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5517_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__0;
    v___f_5518_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__1;
    v___f_5519_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__2;
    v___f_5520_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__3;
    v___f_5521_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__4;
    v___f_5522_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__5;
    v___f_5523_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__6;
    v___x_5524_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5524_, 0, v___f_5517_);
    crate::leanh::lean_ctor_set(v___x_5524_, 1, v___f_5518_);
    v___x_5525_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5525_, 0, v___x_5524_);
    crate::leanh::lean_ctor_set(v___x_5525_, 1, v___f_5519_);
    crate::leanh::lean_ctor_set(v___x_5525_, 2, v___f_5520_);
    crate::leanh::lean_ctor_set(v___x_5525_, 3, v___f_5521_);
    crate::leanh::lean_ctor_set(v___x_5525_, 4, v___f_5522_);
    v___x_5526_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5526_, 0, v___x_5525_);
    crate::leanh::lean_ctor_set(v___x_5526_, 1, v___f_5523_);
    v___x_5527_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7_once
        ),
        _init_l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7,
    );
    v___x_5528_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5529_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5529_, 0, v___x_5527_);
    crate::leanh::lean_ctor_set(v___x_5529_, 1, v___x_5528_);
    v___x_5530_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5530_, 0, v___x_5529_);
    v___x_5531_ = l_instInhabitedOfMonad___redArg(v___x_5526_, v___x_5530_);
    v___x_5532_ = lean_panic_fn_borrowed(v___x_5531_, v_msg_5516_);
    crate::leanh::lean_dec(v___x_5531_);
    return v___x_5532_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__5(
    mut v_msg_5533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5534_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__0;
    v___f_5535_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__1;
    v___f_5536_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__2;
    v___f_5537_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__3;
    v___f_5538_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__4;
    v___f_5539_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__5;
    v___f_5540_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__6;
    v___x_5541_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5541_, 0, v___f_5534_);
    crate::leanh::lean_ctor_set(v___x_5541_, 1, v___f_5535_);
    v___x_5542_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5542_, 0, v___x_5541_);
    crate::leanh::lean_ctor_set(v___x_5542_, 1, v___f_5536_);
    crate::leanh::lean_ctor_set(v___x_5542_, 2, v___f_5537_);
    crate::leanh::lean_ctor_set(v___x_5542_, 3, v___f_5538_);
    crate::leanh::lean_ctor_set(v___x_5542_, 4, v___f_5539_);
    v___x_5543_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5543_, 0, v___x_5542_);
    crate::leanh::lean_ctor_set(v___x_5543_, 1, v___f_5540_);
    v___x_5544_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7_once
        ),
        _init_l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7,
    );
    v___x_5545_ = l_instInhabitedOfMonad___redArg(v___x_5543_, v___x_5544_);
    v___x_5546_ = lean_panic_fn_borrowed(v___x_5545_, v_msg_5533_);
    crate::leanh::lean_dec(v___x_5545_);
    return v___x_5546_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(
    mut v_a_5547_: *mut crate::leanh::LeanObject,
    mut v_x_5548_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5549_: u8 = 0;
    let mut v_key_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5548_) == 0 {
                    v___x_5549_ = 0;
                    return v___x_5549_;
                } else {
                    v_key_5550_ = crate::leanh::lean_ctor_get(v_x_5548_, 0);
                    v_tail_5551_ = crate::leanh::lean_ctor_get(v_x_5548_, 2);
                    v___x_5552_ = lean_name_eq(v_key_5550_, v_a_5547_);
                    if v___x_5552_ == 0 {
                        v_x_5548_ = v_tail_5551_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5552_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg___boxed(
    mut v_a_5554_: *mut crate::leanh::LeanObject,
    mut v_x_5555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5556_: u8 = 0;
    let mut v_r_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5556_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_5554_, v_x_5555_);
    crate::leanh::lean_dec(v_x_5555_);
    crate::leanh::lean_dec(v_a_5554_);
    v_r_5557_ = crate::leanh::lean_box((v_res_5556_) as usize);
    return v_r_5557_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10___redArg(
    mut v_x_5558_: *mut crate::leanh::LeanObject,
    mut v_x_5559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5565_: u8 = 0;
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5568_: u64 = 0;
    let mut v___x_5569_: u64 = 0;
    let mut v___x_5570_: u64 = 0;
    let mut v_fold_5571_: u64 = 0;
    let mut v___x_5572_: u64 = 0;
    let mut v___x_5573_: u64 = 0;
    let mut v___x_5574_: u64 = 0;
    let mut v___x_5575_: usize = 0;
    let mut v___x_5576_: usize = 0;
    let mut v___x_5577_: usize = 0;
    let mut v___x_5578_: usize = 0;
    let mut v___x_5579_: usize = 0;
    let mut v___x_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: u64 = 0;
    let mut v_hash_5587_: u64 = 0;
    let mut v_isSharedCheck_5588_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5559_) == 0 {
                    return v_x_5558_;
                } else {
                    v_key_5560_ = crate::leanh::lean_ctor_get(v_x_5559_, 0);
                    v_value_5561_ = crate::leanh::lean_ctor_get(v_x_5559_, 1);
                    v_tail_5562_ = crate::leanh::lean_ctor_get(v_x_5559_, 2);
                    v_isSharedCheck_5588_ = (!crate::leanh::lean_is_exclusive(v_x_5559_)) as u8;
                    if v_isSharedCheck_5588_ == 0 {
                        v___x_5564_ = v_x_5559_;
                        v_isShared_5565_ = v_isSharedCheck_5588_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5562_);
                        crate::leanh::lean_inc(v_value_5561_);
                        crate::leanh::lean_inc(v_key_5560_);
                        crate::leanh::lean_dec(v_x_5559_);
                        v___x_5564_ = crate::leanh::lean_box(0);
                        v_isShared_5565_ = v_isSharedCheck_5588_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5566_ = lean_array_get_size(v_x_5558_);
                if crate::leanh::lean_obj_tag(v_key_5560_) == 0 {
                    v___x_5586_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
                    v___y_5568_ = v___x_5586_;
                    state = 2;
                    continue;
                } else {
                    v_hash_5587_ = crate::leanh::lean_ctor_get_uint64(
                        v_key_5560_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_5568_ = v_hash_5587_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5569_ = 32u64;
                v___x_5570_ = lean_uint64_shift_right(v___y_5568_, v___x_5569_);
                v_fold_5571_ = lean_uint64_xor(v___y_5568_, v___x_5570_);
                v___x_5572_ = 16u64;
                v___x_5573_ = lean_uint64_shift_right(v_fold_5571_, v___x_5572_);
                v___x_5574_ = lean_uint64_xor(v_fold_5571_, v___x_5573_);
                v___x_5575_ = lean_uint64_to_usize(v___x_5574_);
                v___x_5576_ = lean_usize_of_nat(v___x_5566_);
                v___x_5577_ = 1usize;
                v___x_5578_ = lean_usize_sub(v___x_5576_, v___x_5577_);
                v___x_5579_ = lean_usize_land(v___x_5575_, v___x_5578_);
                v___x_5580_ = lean_array_uget_borrowed(v_x_5558_, v___x_5579_);
                crate::leanh::lean_inc(v___x_5580_);
                if v_isShared_5565_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5564_, 2, v___x_5580_);
                    v___x_5582_ = v___x_5564_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5585_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_key_5560_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5585_, 1, v_value_5561_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5585_, 2, v___x_5580_);
                    v___x_5582_ = v_reuseFailAlloc_5585_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5583_ = lean_array_uset(v_x_5558_, v___x_5579_, v___x_5582_);
                v_x_5558_ = v___x_5583_;
                v_x_5559_ = v_tail_5562_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8___redArg(
    mut v_i_5589_: *mut crate::leanh::LeanObject,
    mut v_source_5590_: *mut crate::leanh::LeanObject,
    mut v_target_5591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: u8 = 0;
    let mut v_es_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5592_ = lean_array_get_size(v_source_5590_);
                v___x_5593_ = lean_nat_dec_lt(v_i_5589_, v___x_5592_);
                if v___x_5593_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_5590_);
                    crate::leanh::lean_dec(v_i_5589_);
                    return v_target_5591_;
                } else {
                    v_es_5594_ = lean_array_fget(v_source_5590_, v_i_5589_);
                    v___x_5595_ = crate::leanh::lean_box(0);
                    v_source_5596_ = lean_array_fset(v_source_5590_, v_i_5589_, v___x_5595_);
                    v_target_5597_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10___redArg(v_target_5591_, v_es_5594_);
                    v___x_5598_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5599_ = lean_nat_add(v_i_5589_, v___x_5598_);
                    crate::leanh::lean_dec(v_i_5589_);
                    v_i_5589_ = v___x_5599_;
                    v_source_5590_ = v_source_5596_;
                    v_target_5591_ = v_target_5597_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(
    mut v_data_5601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5602_ = lean_array_get_size(v_data_5601_);
    v___x_5603_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_5604_ = lean_nat_mul(v___x_5602_, v___x_5603_);
    v___x_5605_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5606_ = crate::leanh::lean_box(0);
    v___x_5607_ = lean_mk_array(v_nbuckets_5604_, v___x_5606_);
    v___x_5608_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8___redArg(v___x_5605_, v_data_5601_, v___x_5607_);
    return v___x_5608_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0___redArg(
    mut v_m_5609_: *mut crate::leanh::LeanObject,
    mut v_a_5610_: *mut crate::leanh::LeanObject,
    mut v_b_5611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5616_: u64 = 0;
    let mut v___x_5617_: u64 = 0;
    let mut v___x_5618_: u64 = 0;
    let mut v_fold_5619_: u64 = 0;
    let mut v___x_5620_: u64 = 0;
    let mut v___x_5621_: u64 = 0;
    let mut v___x_5622_: u64 = 0;
    let mut v___x_5623_: usize = 0;
    let mut v___x_5624_: usize = 0;
    let mut v___x_5625_: usize = 0;
    let mut v___x_5626_: usize = 0;
    let mut v___x_5627_: usize = 0;
    let mut v_bkt_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: u8 = 0;
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5632_: u8 = 0;
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: u8 = 0;
    let mut v_val_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5650_: u8 = 0;
    let mut v_unused_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: u64 = 0;
    let mut v_hash_5654_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5612_ = crate::leanh::lean_ctor_get(v_m_5609_, 0);
                v_buckets_5613_ = crate::leanh::lean_ctor_get(v_m_5609_, 1);
                v___x_5614_ = lean_array_get_size(v_buckets_5613_);
                if crate::leanh::lean_obj_tag(v_a_5610_) == 0 {
                    v___x_5653_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
                    v___y_5616_ = v___x_5653_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5654_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_5610_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_5616_ = v_hash_5654_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5617_ = 32u64;
                v___x_5618_ = lean_uint64_shift_right(v___y_5616_, v___x_5617_);
                v_fold_5619_ = lean_uint64_xor(v___y_5616_, v___x_5618_);
                v___x_5620_ = 16u64;
                v___x_5621_ = lean_uint64_shift_right(v_fold_5619_, v___x_5620_);
                v___x_5622_ = lean_uint64_xor(v_fold_5619_, v___x_5621_);
                v___x_5623_ = lean_uint64_to_usize(v___x_5622_);
                v___x_5624_ = lean_usize_of_nat(v___x_5614_);
                v___x_5625_ = 1usize;
                v___x_5626_ = lean_usize_sub(v___x_5624_, v___x_5625_);
                v___x_5627_ = lean_usize_land(v___x_5623_, v___x_5626_);
                v_bkt_5628_ = lean_array_uget_borrowed(v_buckets_5613_, v___x_5627_);
                v___x_5629_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_5610_, v_bkt_5628_);
                if v___x_5629_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_5613_);
                    crate::leanh::lean_inc(v_size_5612_);
                    v_isSharedCheck_5650_ = (!crate::leanh::lean_is_exclusive(v_m_5609_)) as u8;
                    if v_isSharedCheck_5650_ == 0 {
                        v_unused_5651_ = crate::leanh::lean_ctor_get(v_m_5609_, 1);
                        crate::leanh::lean_dec(v_unused_5651_);
                        v_unused_5652_ = crate::leanh::lean_ctor_get(v_m_5609_, 0);
                        crate::leanh::lean_dec(v_unused_5652_);
                        v___x_5631_ = v_m_5609_;
                        v_isShared_5632_ = v_isSharedCheck_5650_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_5609_);
                        v___x_5631_ = crate::leanh::lean_box(0);
                        v_isShared_5632_ = v_isSharedCheck_5650_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_5611_);
                    crate::leanh::lean_dec(v_a_5610_);
                    return v_m_5609_;
                }
            }
            2 => {
                v___x_5633_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_5634_ = lean_nat_add(v_size_5612_, v___x_5633_);
                crate::leanh::lean_dec(v_size_5612_);
                crate::leanh::lean_inc(v_bkt_5628_);
                v___x_5635_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5635_, 0, v_a_5610_);
                crate::leanh::lean_ctor_set(v___x_5635_, 1, v_b_5611_);
                crate::leanh::lean_ctor_set(v___x_5635_, 2, v_bkt_5628_);
                v_buckets_x27_5636_ = lean_array_uset(v_buckets_5613_, v___x_5627_, v___x_5635_);
                v___x_5637_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_5638_ = lean_nat_mul(v_size_x27_5634_, v___x_5637_);
                v___x_5639_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_5640_ = lean_nat_div(v___x_5638_, v___x_5639_);
                crate::leanh::lean_dec(v___x_5638_);
                v___x_5641_ = lean_array_get_size(v_buckets_x27_5636_);
                v___x_5642_ = lean_nat_dec_le(v___x_5640_, v___x_5641_);
                crate::leanh::lean_dec(v___x_5640_);
                if v___x_5642_ == 0 {
                    v_val_5643_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(v_buckets_x27_5636_);
                    if v_isShared_5632_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5631_, 1, v_val_5643_);
                        crate::leanh::lean_ctor_set(v___x_5631_, 0, v_size_x27_5634_);
                        v___x_5645_ = v___x_5631_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5646_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5646_, 0, v_size_x27_5634_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5646_, 1, v_val_5643_);
                        v___x_5645_ = v_reuseFailAlloc_5646_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_5632_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5631_, 1, v_buckets_x27_5636_);
                        crate::leanh::lean_ctor_set(v___x_5631_, 0, v_size_x27_5634_);
                        v___x_5648_ = v___x_5631_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5649_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5649_, 0, v_size_x27_5634_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5649_, 1, v_buckets_x27_5636_);
                        v___x_5648_ = v_reuseFailAlloc_5649_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5645_;
            }
            4 => {
                return v___x_5648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1(
    mut v_as_5655_: *mut crate::leanh::LeanObject,
    mut v_sz_5656_: usize,
    mut v_i_5657_: usize,
    mut v_b_5658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5659_: u8 = 0;
    let mut v_a_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: usize = 0;
    let mut v___x_5664_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5659_ = lean_usize_dec_lt(v_i_5657_, v_sz_5656_);
                if v___x_5659_ == 0 {
                    return v_b_5658_;
                } else {
                    v_a_5660_ = lean_array_uget_borrowed(v_as_5655_, v_i_5657_);
                    v___x_5661_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_a_5660_);
                    v_r_5662_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0___redArg(v_b_5658_, v_a_5660_, v___x_5661_);
                    v___x_5663_ = 1usize;
                    v___x_5664_ = lean_usize_add(v_i_5657_, v___x_5663_);
                    v_i_5657_ = v___x_5664_;
                    v_b_5658_ = v_r_5662_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1___boxed(
    mut v_as_5666_: *mut crate::leanh::LeanObject,
    mut v_sz_5667_: *mut crate::leanh::LeanObject,
    mut v_i_5668_: *mut crate::leanh::LeanObject,
    mut v_b_5669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5670_: usize = 0;
    let mut v_i_boxed_5671_: usize = 0;
    let mut v_res_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5670_ = crate::leanh::lean_unbox_usize(v_sz_5667_);
    crate::leanh::lean_dec(v_sz_5667_);
    v_i_boxed_5671_ = crate::leanh::lean_unbox_usize(v_i_5668_);
    crate::leanh::lean_dec(v_i_5668_);
    v_res_5672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1(v_as_5666_, v_sz_boxed_5670_, v_i_boxed_5671_, v_b_5669_);
    crate::leanh::lean_dec_ref(v_as_5666_);
    return v_res_5672_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0(
    mut v_m_5673_: *mut crate::leanh::LeanObject,
    mut v_l_5674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_5675_: usize = 0;
    let mut v___x_5676_: usize = 0;
    let mut v___x_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_5675_ = lean_array_size(v_l_5674_);
    v___x_5676_ = 0usize;
    v___x_5677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1(v_l_5674_, v_sz_5675_, v___x_5676_, v_m_5673_);
    return v___x_5677_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0___boxed(
    mut v_m_5678_: *mut crate::leanh::LeanObject,
    mut v_l_5679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5680_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0(v_m_5678_, v_l_5679_);
    crate::leanh::lean_dec_ref(v_l_5679_);
    return v_res_5680_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(
    mut v_m_5681_: *mut crate::leanh::LeanObject,
    mut v_a_5682_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5686_: u64 = 0;
    let mut v___x_5687_: u64 = 0;
    let mut v___x_5688_: u64 = 0;
    let mut v_fold_5689_: u64 = 0;
    let mut v___x_5690_: u64 = 0;
    let mut v___x_5691_: u64 = 0;
    let mut v___x_5692_: u64 = 0;
    let mut v___x_5693_: usize = 0;
    let mut v___x_5694_: usize = 0;
    let mut v___x_5695_: usize = 0;
    let mut v___x_5696_: usize = 0;
    let mut v___x_5697_: usize = 0;
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: u8 = 0;
    let mut v___x_5700_: u64 = 0;
    let mut v_hash_5701_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_5683_ = crate::leanh::lean_ctor_get(v_m_5681_, 1);
                v___x_5684_ = lean_array_get_size(v_buckets_5683_);
                if crate::leanh::lean_obj_tag(v_a_5682_) == 0 {
                    v___x_5700_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
                    v___y_5686_ = v___x_5700_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5701_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_5682_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_5686_ = v_hash_5701_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5687_ = 32u64;
                v___x_5688_ = lean_uint64_shift_right(v___y_5686_, v___x_5687_);
                v_fold_5689_ = lean_uint64_xor(v___y_5686_, v___x_5688_);
                v___x_5690_ = 16u64;
                v___x_5691_ = lean_uint64_shift_right(v_fold_5689_, v___x_5690_);
                v___x_5692_ = lean_uint64_xor(v_fold_5689_, v___x_5691_);
                v___x_5693_ = lean_uint64_to_usize(v___x_5692_);
                v___x_5694_ = lean_usize_of_nat(v___x_5684_);
                v___x_5695_ = 1usize;
                v___x_5696_ = lean_usize_sub(v___x_5694_, v___x_5695_);
                v___x_5697_ = lean_usize_land(v___x_5693_, v___x_5696_);
                v___x_5698_ = lean_array_uget_borrowed(v_buckets_5683_, v___x_5697_);
                v___x_5699_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_5682_, v___x_5698_);
                return v___x_5699_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg___boxed(
    mut v_m_5702_: *mut crate::leanh::LeanObject,
    mut v_a_5703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5704_: u8 = 0;
    let mut v_r_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5704_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(v_m_5702_, v_a_5703_);
    crate::leanh::lean_dec(v_a_5703_);
    crate::leanh::lean_dec_ref(v_m_5702_);
    v_r_5705_ = crate::leanh::lean_box((v_res_5704_) as usize);
    return v_r_5705_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(
    mut v_a_5706_: *mut crate::leanh::LeanObject,
    mut v_b_5707_: *mut crate::leanh::LeanObject,
    mut v_x_5708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5714_: u8 = 0;
    let mut v___x_5715_: u8 = 0;
    let mut v___x_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5723_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5708_) == 0 {
                    crate::leanh::lean_dec(v_b_5707_);
                    crate::leanh::lean_dec(v_a_5706_);
                    return v_x_5708_;
                } else {
                    v_key_5709_ = crate::leanh::lean_ctor_get(v_x_5708_, 0);
                    v_value_5710_ = crate::leanh::lean_ctor_get(v_x_5708_, 1);
                    v_tail_5711_ = crate::leanh::lean_ctor_get(v_x_5708_, 2);
                    v_isSharedCheck_5723_ = (!crate::leanh::lean_is_exclusive(v_x_5708_)) as u8;
                    if v_isSharedCheck_5723_ == 0 {
                        v___x_5713_ = v_x_5708_;
                        v_isShared_5714_ = v_isSharedCheck_5723_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5711_);
                        crate::leanh::lean_inc(v_value_5710_);
                        crate::leanh::lean_inc(v_key_5709_);
                        crate::leanh::lean_dec(v_x_5708_);
                        v___x_5713_ = crate::leanh::lean_box(0);
                        v_isShared_5714_ = v_isSharedCheck_5723_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5715_ = lean_name_eq(v_key_5709_, v_a_5706_);
                if v___x_5715_ == 0 {
                    v___x_5716_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(v_a_5706_, v_b_5707_, v_tail_5711_);
                    if v_isShared_5714_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5713_, 2, v___x_5716_);
                        v___x_5718_ = v___x_5713_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5719_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5719_, 0, v_key_5709_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5719_, 1, v_value_5710_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5719_, 2, v___x_5716_);
                        v___x_5718_ = v_reuseFailAlloc_5719_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_5710_);
                    crate::leanh::lean_dec(v_key_5709_);
                    if v_isShared_5714_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5713_, 1, v_b_5707_);
                        crate::leanh::lean_ctor_set(v___x_5713_, 0, v_a_5706_);
                        v___x_5721_ = v___x_5713_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5722_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5722_, 0, v_a_5706_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5722_, 1, v_b_5707_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5722_, 2, v_tail_5711_);
                        v___x_5721_ = v_reuseFailAlloc_5722_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5718_;
            }
            3 => {
                return v___x_5721_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3___redArg(
    mut v_m_5724_: *mut crate::leanh::LeanObject,
    mut v_a_5725_: *mut crate::leanh::LeanObject,
    mut v_b_5726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5731_: u8 = 0;
    let mut v___x_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5734_: u64 = 0;
    let mut v___x_5735_: u64 = 0;
    let mut v___x_5736_: u64 = 0;
    let mut v_fold_5737_: u64 = 0;
    let mut v___x_5738_: u64 = 0;
    let mut v___x_5739_: u64 = 0;
    let mut v___x_5740_: u64 = 0;
    let mut v___x_5741_: usize = 0;
    let mut v___x_5742_: usize = 0;
    let mut v___x_5743_: usize = 0;
    let mut v___x_5744_: usize = 0;
    let mut v___x_5745_: usize = 0;
    let mut v_bkt_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: u8 = 0;
    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: u8 = 0;
    let mut v_val_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: u64 = 0;
    let mut v_hash_5773_: u64 = 0;
    let mut v_isSharedCheck_5774_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5727_ = crate::leanh::lean_ctor_get(v_m_5724_, 0);
                v_buckets_5728_ = crate::leanh::lean_ctor_get(v_m_5724_, 1);
                v_isSharedCheck_5774_ = (!crate::leanh::lean_is_exclusive(v_m_5724_)) as u8;
                if v_isSharedCheck_5774_ == 0 {
                    v___x_5730_ = v_m_5724_;
                    v_isShared_5731_ = v_isSharedCheck_5774_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_5728_);
                    crate::leanh::lean_inc(v_size_5727_);
                    crate::leanh::lean_dec(v_m_5724_);
                    v___x_5730_ = crate::leanh::lean_box(0);
                    v_isShared_5731_ = v_isSharedCheck_5774_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5732_ = lean_array_get_size(v_buckets_5728_);
                if crate::leanh::lean_obj_tag(v_a_5725_) == 0 {
                    v___x_5772_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
                    v___y_5734_ = v___x_5772_;
                    state = 2;
                    continue;
                } else {
                    v_hash_5773_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_5725_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_5734_ = v_hash_5773_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5735_ = 32u64;
                v___x_5736_ = lean_uint64_shift_right(v___y_5734_, v___x_5735_);
                v_fold_5737_ = lean_uint64_xor(v___y_5734_, v___x_5736_);
                v___x_5738_ = 16u64;
                v___x_5739_ = lean_uint64_shift_right(v_fold_5737_, v___x_5738_);
                v___x_5740_ = lean_uint64_xor(v_fold_5737_, v___x_5739_);
                v___x_5741_ = lean_uint64_to_usize(v___x_5740_);
                v___x_5742_ = lean_usize_of_nat(v___x_5732_);
                v___x_5743_ = 1usize;
                v___x_5744_ = lean_usize_sub(v___x_5742_, v___x_5743_);
                v___x_5745_ = lean_usize_land(v___x_5741_, v___x_5744_);
                v_bkt_5746_ = lean_array_uget_borrowed(v_buckets_5728_, v___x_5745_);
                v___x_5747_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_5725_, v_bkt_5746_);
                if v___x_5747_ == 0 {
                    v___x_5748_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_5749_ = lean_nat_add(v_size_5727_, v___x_5748_);
                    crate::leanh::lean_dec(v_size_5727_);
                    crate::leanh::lean_inc(v_bkt_5746_);
                    v___x_5750_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5750_, 0, v_a_5725_);
                    crate::leanh::lean_ctor_set(v___x_5750_, 1, v_b_5726_);
                    crate::leanh::lean_ctor_set(v___x_5750_, 2, v_bkt_5746_);
                    v_buckets_x27_5751_ =
                        lean_array_uset(v_buckets_5728_, v___x_5745_, v___x_5750_);
                    v___x_5752_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_5753_ = lean_nat_mul(v_size_x27_5749_, v___x_5752_);
                    v___x_5754_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_5755_ = lean_nat_div(v___x_5753_, v___x_5754_);
                    crate::leanh::lean_dec(v___x_5753_);
                    v___x_5756_ = lean_array_get_size(v_buckets_x27_5751_);
                    v___x_5757_ = lean_nat_dec_le(v___x_5755_, v___x_5756_);
                    crate::leanh::lean_dec(v___x_5755_);
                    if v___x_5757_ == 0 {
                        v_val_5758_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(v_buckets_x27_5751_);
                        if v_isShared_5731_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5730_, 1, v_val_5758_);
                            crate::leanh::lean_ctor_set(v___x_5730_, 0, v_size_x27_5749_);
                            v___x_5760_ = v___x_5730_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5761_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_5761_,
                                0,
                                v_size_x27_5749_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5761_, 1, v_val_5758_);
                            v___x_5760_ = v_reuseFailAlloc_5761_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_5731_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5730_, 1, v_buckets_x27_5751_);
                            crate::leanh::lean_ctor_set(v___x_5730_, 0, v_size_x27_5749_);
                            v___x_5763_ = v___x_5730_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5764_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_5764_,
                                0,
                                v_size_x27_5749_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_5764_,
                                1,
                                v_buckets_x27_5751_,
                            );
                            v___x_5763_ = v_reuseFailAlloc_5764_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_5746_);
                    v___x_5765_ = crate::leanh::lean_box(0);
                    v_buckets_x27_5766_ =
                        lean_array_uset(v_buckets_5728_, v___x_5745_, v___x_5765_);
                    v___x_5767_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(v_a_5725_, v_b_5726_, v_bkt_5746_);
                    v___x_5768_ = lean_array_uset(v_buckets_x27_5766_, v___x_5745_, v___x_5767_);
                    if v_isShared_5731_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5730_, 1, v___x_5768_);
                        v___x_5770_ = v___x_5730_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5771_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5771_, 0, v_size_5727_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5771_, 1, v___x_5768_);
                        v___x_5770_ = v_reuseFailAlloc_5771_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5760_;
            }
            4 => {
                return v___x_5763_;
            }
            5 => {
                return v___x_5770_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5778_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__2;
    v___x_5779_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_5780_ = crate::leanh::lean_unsigned_to_nat(238);
    v___x_5781_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__1;
    v___x_5782_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__0;
    v___x_5783_ = l_mkPanicMessageWithDecl(
        v___x_5782_,
        v___x_5781_,
        v___x_5780_,
        v___x_5779_,
        v___x_5778_,
    );
    return v___x_5783_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(
    mut v___x_5784_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5785_: *mut crate::leanh::LeanObject,
    mut v_b_5786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5793_: u8 = 0;
    let mut v_map_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: u8 = 0;
    let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: u8 = 0;
    let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5811_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_5785_) == 0 {
                    return v_b_5786_;
                } else {
                    v_head_5787_ = crate::leanh::lean_ctor_get(v_as_x27_5785_, 0);
                    v_tail_5788_ = crate::leanh::lean_ctor_get(v_as_x27_5785_, 1);
                    v_fst_5789_ = crate::leanh::lean_ctor_get(v_b_5786_, 0);
                    v_snd_5790_ = crate::leanh::lean_ctor_get(v_b_5786_, 1);
                    v_isSharedCheck_5811_ = (!crate::leanh::lean_is_exclusive(v_b_5786_)) as u8;
                    if v_isSharedCheck_5811_ == 0 {
                        v___x_5792_ = v_b_5786_;
                        v_isShared_5793_ = v_isSharedCheck_5811_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5790_);
                        crate::leanh::lean_inc(v_fst_5789_);
                        crate::leanh::lean_dec(v_b_5786_);
                        v___x_5792_ = crate::leanh::lean_box(0);
                        v_isShared_5793_ = v_isSharedCheck_5811_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5809_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(v___x_5784_, v_head_5787_);
                if v___x_5809_ == 0 {
                    v_map_5795_ = v_fst_5789_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5790_);
                    crate::leanh::lean_inc(v_head_5787_);
                    v___x_5810_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3___redArg(v_fst_5789_, v_head_5787_, v_snd_5790_);
                    v_map_5795_ = v___x_5810_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5796_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5797_ = lean_nat_dec_eq(v_snd_5790_, v___x_5796_);
                if v___x_5797_ == 0 {
                    v___x_5798_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5799_ = lean_nat_sub(v_snd_5790_, v___x_5798_);
                    crate::leanh::lean_dec(v_snd_5790_);
                    if v_isShared_5793_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5792_, 1, v___x_5799_);
                        crate::leanh::lean_ctor_set(v___x_5792_, 0, v_map_5795_);
                        v___x_5801_ = v___x_5792_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5803_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 0, v_map_5795_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 1, v___x_5799_);
                        v___x_5801_ = v_reuseFailAlloc_5803_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_map_5795_);
                    crate::leanh::lean_del_object(v___x_5792_);
                    crate::leanh::lean_dec(v_snd_5790_);
                    v___x_5804_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3_once), _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3);
                    v___x_5805_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1(
                        v___x_5804_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5805_) == 0 {
                        v_a_5806_ = crate::leanh::lean_ctor_get(v___x_5805_, 0);
                        crate::leanh::lean_inc(v_a_5806_);
                        crate::leanh::lean_dec_ref_known(v___x_5805_, 1);
                        return v_a_5806_;
                    } else {
                        v_a_5807_ = crate::leanh::lean_ctor_get(v___x_5805_, 0);
                        crate::leanh::lean_inc(v_a_5807_);
                        crate::leanh::lean_dec_ref_known(v___x_5805_, 1);
                        v_as_x27_5785_ = v_tail_5788_;
                        v_b_5786_ = v_a_5807_;
                        state = 0;
                        continue;
                    }
                }
            }
            3 => {
                v_as_x27_5785_ = v_tail_5788_;
                v_b_5786_ = v___x_5801_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___boxed(
    mut v___x_5812_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5813_: *mut crate::leanh::LeanObject,
    mut v_b_5814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5815_ =
        l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(
            v___x_5812_,
            v_as_x27_5813_,
            v_b_5814_,
        );
    crate::leanh::lean_dec(v_as_x27_5813_);
    crate::leanh::lean_dec_ref(v___x_5812_);
    return v_res_5815_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5816_ = crate::leanh::lean_box(0);
    v___x_5817_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_5818_ = lean_mk_array(v___x_5817_, v___x_5816_);
    return v___x_5818_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5819_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0_once),
        _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0,
    );
    v___x_5820_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5821_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5821_, 0, v___x_5820_);
    crate::leanh::lean_ctor_set(v___x_5821_, 1, v___x_5819_);
    return v___x_5821_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5823_ = l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__2;
    v___x_5824_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_5825_ = crate::leanh::lean_unsigned_to_nat(240);
    v___x_5826_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__1;
    v___x_5827_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__0;
    v___x_5828_ = l_mkPanicMessageWithDecl(
        v___x_5827_,
        v___x_5826_,
        v___x_5825_,
        v___x_5824_,
        v___x_5823_,
    );
    return v___x_5828_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getImpureDeclIndices(
    mut v_env_5829_: *mut crate::leanh::LeanObject,
    mut v_targets_5830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5840_: u8 = 0;
    let mut v___y_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: u8 = 0;
    let mut v___x_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5866_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5831_ = l_Lean_Compiler_LCNF_declOrderExt;
                v_asyncMode_5832_ = crate::leanh::lean_ctor_get(v___x_5831_, 2);
                v___x_5833_ = l_Lean_Compiler_LCNF_isDeclTransparent___closed__0;
                v___x_5834_ = crate::leanh::lean_box(0);
                v___x_5835_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_5833_,
                        v___x_5831_,
                        v_env_5829_,
                        v_asyncMode_5832_,
                        v___x_5834_,
                    );
                v_fst_5836_ = crate::leanh::lean_ctor_get(v___x_5835_, 0);
                v_snd_5837_ = crate::leanh::lean_ctor_get(v___x_5835_, 1);
                v_isSharedCheck_5866_ = (!crate::leanh::lean_is_exclusive(v___x_5835_)) as u8;
                if v_isSharedCheck_5866_ == 0 {
                    v___x_5839_ = v___x_5835_;
                    v_isShared_5840_ = v_isSharedCheck_5866_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5837_);
                    crate::leanh::lean_inc(v_fst_5836_);
                    crate::leanh::lean_dec(v___x_5835_);
                    v___x_5839_ = crate::leanh::lean_box(0);
                    v_isShared_5840_ = v_isSharedCheck_5866_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_snd_5837_) == 0 {
                    v_size_5864_ = crate::leanh::lean_ctor_get(v_snd_5837_, 0);
                    crate::leanh::lean_inc(v_size_5864_);
                    crate::leanh::lean_dec_ref_known(v_snd_5837_, 5);
                    v___y_5842_ = v_size_5864_;
                    state = 2;
                    continue;
                } else {
                    v___x_5865_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5842_ = v___x_5865_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5843_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5844_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_5845_ = lean_nat_mul(v___y_5842_, v___x_5844_);
                v___x_5846_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_5847_ = lean_nat_div(v___x_5845_, v___x_5846_);
                crate::leanh::lean_dec(v___x_5845_);
                v___x_5848_ = l_Nat_nextPowerOfTwo(v___x_5847_);
                crate::leanh::lean_dec(v___x_5847_);
                v___x_5849_ = crate::leanh::lean_box(0);
                v___x_5850_ = lean_mk_array(v___x_5848_, v___x_5849_);
                v_map_5851_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_map_5851_, 0, v___x_5843_);
                crate::leanh::lean_ctor_set(v_map_5851_, 1, v___x_5850_);
                v___x_5852_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1,
                );
                v___x_5853_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0(v___x_5852_, v_targets_5830_);
                if v_isShared_5840_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5839_, 1, v___y_5842_);
                    crate::leanh::lean_ctor_set(v___x_5839_, 0, v_map_5851_);
                    v___x_5855_ = v___x_5839_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5863_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5863_, 0, v_map_5851_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5863_, 1, v___y_5842_);
                    v___x_5855_ = v_reuseFailAlloc_5863_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5856_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(v___x_5853_, v_fst_5836_, v___x_5855_);
                crate::leanh::lean_dec(v_fst_5836_);
                crate::leanh::lean_dec_ref(v___x_5853_);
                v_fst_5857_ = crate::leanh::lean_ctor_get(v___x_5856_, 0);
                crate::leanh::lean_inc(v_fst_5857_);
                crate::leanh::lean_dec_ref(v___x_5856_);
                v_size_5858_ = crate::leanh::lean_ctor_get(v_fst_5857_, 0);
                v___x_5859_ = lean_array_get_size(v_targets_5830_);
                v___x_5860_ = lean_nat_dec_eq(v_size_5858_, v___x_5859_);
                if v___x_5860_ == 0 {
                    crate::leanh::lean_dec(v_fst_5857_);
                    v___x_5861_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3_once
                        ),
                        _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3,
                    );
                    v___x_5862_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__5(
                        v___x_5861_,
                    );
                    return v___x_5862_;
                } else {
                    return v_fst_5857_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getImpureDeclIndices___boxed(
    mut v_env_5867_: *mut crate::leanh::LeanObject,
    mut v_targets_5868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5869_ = l_Lean_Compiler_LCNF_getImpureDeclIndices(v_env_5867_, v_targets_5868_);
    crate::leanh::lean_dec_ref(v_targets_5868_);
    return v_res_5869_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2(
    mut v_00_u03b2_5870_: *mut crate::leanh::LeanObject,
    mut v_m_5871_: *mut crate::leanh::LeanObject,
    mut v_a_5872_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5873_: u8 = 0;
    v___x_5873_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(v_m_5871_, v_a_5872_);
    return v___x_5873_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___boxed(
    mut v_00_u03b2_5874_: *mut crate::leanh::LeanObject,
    mut v_m_5875_: *mut crate::leanh::LeanObject,
    mut v_a_5876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5877_: u8 = 0;
    let mut v_r_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5877_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2(v_00_u03b2_5874_, v_m_5875_, v_a_5876_);
    crate::leanh::lean_dec(v_a_5876_);
    crate::leanh::lean_dec_ref(v_m_5875_);
    v_r_5878_ = crate::leanh::lean_box((v_res_5877_) as usize);
    return v_r_5878_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3(
    mut v_00_u03b2_5879_: *mut crate::leanh::LeanObject,
    mut v_m_5880_: *mut crate::leanh::LeanObject,
    mut v_a_5881_: *mut crate::leanh::LeanObject,
    mut v_b_5882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5883_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3___redArg(v_m_5880_, v_a_5881_, v_b_5882_);
    return v___x_5883_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4(
    mut v___x_5884_: *mut crate::leanh::LeanObject,
    mut v_as_5885_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5886_: *mut crate::leanh::LeanObject,
    mut v_b_5887_: *mut crate::leanh::LeanObject,
    mut v_a_5888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5889_ =
        l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(
            v___x_5884_,
            v_as_x27_5886_,
            v_b_5887_,
        );
    return v___x_5889_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___boxed(
    mut v___x_5890_: *mut crate::leanh::LeanObject,
    mut v_as_5891_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5892_: *mut crate::leanh::LeanObject,
    mut v_b_5893_: *mut crate::leanh::LeanObject,
    mut v_a_5894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5895_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4(
        v___x_5890_,
        v_as_5891_,
        v_as_x27_5892_,
        v_b_5893_,
        v_a_5894_,
    );
    crate::leanh::lean_dec(v_as_x27_5892_);
    crate::leanh::lean_dec(v_as_5891_);
    crate::leanh::lean_dec_ref(v___x_5890_);
    return v_res_5895_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0(
    mut v_00_u03b2_5896_: *mut crate::leanh::LeanObject,
    mut v_m_5897_: *mut crate::leanh::LeanObject,
    mut v_a_5898_: *mut crate::leanh::LeanObject,
    mut v_b_5899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5900_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0___redArg(v_m_5897_, v_a_5898_, v_b_5899_);
    return v___x_5900_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4(
    mut v_00_u03b2_5901_: *mut crate::leanh::LeanObject,
    mut v_a_5902_: *mut crate::leanh::LeanObject,
    mut v_x_5903_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5904_: u8 = 0;
    v___x_5904_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_5902_, v_x_5903_);
    return v___x_5904_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___boxed(
    mut v_00_u03b2_5905_: *mut crate::leanh::LeanObject,
    mut v_a_5906_: *mut crate::leanh::LeanObject,
    mut v_x_5907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5908_: u8 = 0;
    let mut v_r_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5908_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4(v_00_u03b2_5905_, v_a_5906_, v_x_5907_);
    crate::leanh::lean_dec(v_x_5907_);
    crate::leanh::lean_dec(v_a_5906_);
    v_r_5909_ = crate::leanh::lean_box((v_res_5908_) as usize);
    return v_r_5909_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6(
    mut v_00_u03b2_5910_: *mut crate::leanh::LeanObject,
    mut v_data_5911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5912_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(v_data_5911_);
    return v___x_5912_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7(
    mut v_00_u03b2_5913_: *mut crate::leanh::LeanObject,
    mut v_a_5914_: *mut crate::leanh::LeanObject,
    mut v_b_5915_: *mut crate::leanh::LeanObject,
    mut v_x_5916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5917_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(v_a_5914_, v_b_5915_, v_x_5916_);
    return v___x_5917_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8(
    mut v_00_u03b2_5918_: *mut crate::leanh::LeanObject,
    mut v_i_5919_: *mut crate::leanh::LeanObject,
    mut v_source_5920_: *mut crate::leanh::LeanObject,
    mut v_target_5921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5922_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8___redArg(v_i_5919_, v_source_5920_, v_target_5921_);
    return v___x_5922_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10(
    mut v_00_u03b2_5923_: *mut crate::leanh::LeanObject,
    mut v_x_5924_: *mut crate::leanh::LeanObject,
    mut v_x_5925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5926_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10___redArg(v_x_5924_, v_x_5925_);
    return v___x_5926_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_PhaseExt(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3496178540____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_baseTransparentDeclsExt =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_baseTransparentDeclsExt,
    );
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1977385844____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_monoTransparentDeclsExt =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_monoTransparentDeclsExt,
    );
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_975450157____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_impureTransparentDeclsExt =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_impureTransparentDeclsExt,
    );
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_LCNF_baseExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_baseExt);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_LCNF_monoExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_monoExt);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_LCNF_impureExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_impureExt);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_LCNF_impureSigExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_impureSigExt);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_LCNF_declOrderExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_declOrderExt);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_PhaseExt(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Compiler_LCNF_mkDeclExt___auto__1 = _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1();
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_mkDeclExt___auto__1);
    l_Lean_Compiler_LCNF_mkSigDeclExt___auto__1 =
        _init_l_Lean_Compiler_LCNF_mkSigDeclExt___auto__1();
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_mkSigDeclExt___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_PhaseExt(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
}

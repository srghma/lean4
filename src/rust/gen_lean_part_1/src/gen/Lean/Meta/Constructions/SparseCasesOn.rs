// Lean compiler output
// Module: Lean.Meta.Constructions.SparseCasesOn
// Imports: Lean.Meta.Basic Lean.AddDecl Lean.Meta.Constructions.CtorIdx Lean.Meta.HasNotBit Lean.Meta.Transform
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_mk, lean_array_pop, lean_array_push,
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_infer_type,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_uint64_mix_hash, lean_uint64_of_nat,
    lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le, lean_usize_dec_lt,
    lean_usize_land, lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::{
    l_Array_toSubarray___redArg, l_Subarray_get___redArg,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_replaceRef, l_List_lengthTR___redArg,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AddDecl::{
    initialize_Lean_AddDecl, l_Lean_addDecl, runtime_initialize_Lean_AddDecl,
};
use crate::r#gen::Lean::AuxRecursor::{l_Lean_markSparseCasesOn, l_Lean_mkCasesOnName};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Core_mkFreshUserName, l_Lean_DeclNameGenerator_mkUniqueName,
    l_Lean_enableRealizationsForConst,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg, l_Lean_PersistentHashMap_instInhabited,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Declaration::{
    l_Lean_ConstantInfo_hasValue, l_Lean_ConstantInfo_levelParams, l_Lean_ConstantInfo_type,
    l_Lean_ConstantInfo_value_x21,
};
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_MapDeclarationExtension_find_x3f___redArg,
    l_Lean_MapDeclarationExtension_insert___redArg, l_Lean_mkMapDeclarationExtension___redArg,
};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_AsyncConstantInfo_toConstantInfo, l_Lean_EnvExtension_modifyState___redArg,
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f, l_Lean_Environment_findAsync_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_hasUnsafe,
    l_Lean_Environment_header, l_Lean_Environment_setExporting,
    l_Lean_EnvironmentHeader_moduleNames, l_Lean_registerEnvExtension___redArg,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_instInhabitedExpr, l_Lean_mkAppN, l_Lean_mkConst,
    l_Lean_mkForall, l_Lean_mkRawNatLit,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed, l_Lean_Meta_mkForallFVars,
    l_Lean_Meta_mkLambdaFVars, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::Constructions::CtorIdx::{
    initialize_Lean_Meta_Constructions_CtorIdx, l_mkCtorIdxName,
    runtime_initialize_Lean_Meta_Constructions_CtorIdx,
};
use crate::r#gen::Lean::Meta::HasNotBit::{
    initialize_Lean_Meta_HasNotBit, l_mkHasNotBit, l_mkHasNotBitProof,
    runtime_initialize_Lean_Meta_HasNotBit,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_inferArgumentTypesN;
use crate::r#gen::Lean::Meta::Transform::{
    initialize_Lean_Meta_Transform, l_Lean_Core_betaReduce, runtime_initialize_Lean_Meta_Transform,
};
use crate::r#gen::Lean::MonadEnv::l_Lean_isInductiveCore_x3f;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ReducibilityAttrs::l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___closed__0: u64 = 0;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0_value:
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
static mut l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedSparseCasesOnInfo_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedSparseCasesOnInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [67, 111, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6298619751691480032 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [83, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 0]};
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject,457590468051701308 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,15120589786868885085 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15105543596597268456 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7412905926462493476 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [115, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 73, 110, 102, 111, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12893803784582653703 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 3 }, m_objs: [0 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16___closed__0_value:
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
    m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [96, 0],
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2_value:
    leanh::LeanStringObject<23> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116,
        111, 114, 0,
    ],
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0],
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [76, 101, 97, 110, 46, 105, 115, 67, 116, 111, 114, 63, 0],
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6_value
) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0_value: leanh::LeanStringObject<
    2,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [104, 0],
};
static mut l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0_value)
                as *mut leanh::LeanObject,
            8738205681931236784 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [101, 108, 115, 101, 0],
};
static mut l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2_value)
                as *mut leanh::LeanObject,
            14862567521649265869 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4_value: leanh::LeanArrayObject<
    0,
> = leanh::LeanArrayObject {
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
static mut l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5_value: leanh::LeanStringObject<
    62,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 62,
    m_capacity: 62,
    m_length: 61,
    m_data: [
        109, 107, 83, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 58, 32, 117, 110,
        101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32,
        112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 105, 110, 32, 116, 121, 112, 101, 32,
        111, 102, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__0_value: leanh::LeanStringObject<30> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [109, 107, 83, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 58, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__2_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 111, 102, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__0_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkSparseCasesOn___closed__0_value: leanh::LeanStringObject<38> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 38,
        m_capacity: 38,
        m_length: 37,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 110, 115, 116, 114, 117, 99, 116,
            105, 111, 110, 115, 46, 83, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 0,
        ],
    };
static mut l_Lean_Meta_mkSparseCasesOn___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSparseCasesOn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkSparseCasesOn___closed__1_value: leanh::LeanStringObject<26> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 109, 107, 83, 112, 97, 114, 115, 101, 67,
            97, 115, 101, 115, 79, 110, 0,
        ],
    };
static mut l_Lean_Meta_mkSparseCasesOn___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSparseCasesOn___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_mkSparseCasesOn___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSparseCasesOn___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkSparseCasesOn___closed__3_value: leanh::LeanStringObject<63> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 63,
        m_capacity: 63,
        m_length: 62,
        m_data: [
            109, 107, 83, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 58, 32, 117, 110,
            101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102,
            32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101,
            114, 115, 32, 105, 110, 32, 96, 0,
        ],
    };
static mut l_Lean_Meta_mkSparseCasesOn___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSparseCasesOn___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_mkSparseCasesOn___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSparseCasesOn___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkSparseCasesOn___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSparseCasesOn___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkSparseCasesOn___closed__6_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            95, 115, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 0,
        ],
    };
static mut l_Lean_Meta_mkSparseCasesOn___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSparseCasesOn___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkSparseCasesOn___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkSparseCasesOn___closed__6_value)
                as *mut leanh::LeanObject,
            9771684452125860719 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkSparseCasesOn___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSparseCasesOn___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_mkSparseCasesOn___closed__8_value: leanh::LeanStringObject<60> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 60,
        m_capacity: 60,
        m_length: 59,
        m_data: [
            109, 107, 83, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 58, 32, 114, 101,
            113, 117, 101, 115, 116, 101, 100, 32, 99, 97, 115, 101, 115, 79, 110, 32, 99, 111,
            109, 98, 105, 110, 97, 116, 111, 114, 32, 105, 115, 32, 110, 111, 116, 32, 115, 112,
            97, 114, 115, 101, 0,
        ],
    };
static mut l_Lean_Meta_mkSparseCasesOn___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSparseCasesOn___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_mkSparseCasesOn___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkSparseCasesOn___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(
    mut v_xs_2406_: *mut leanh::LeanObject,
    mut v_ys_2407_: *mut leanh::LeanObject,
    mut v_x_2408_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2410_: u8 = 0;
    let mut v_one_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2409_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_2410_ = lean_nat_dec_eq(v_x_2408_, v_zero_2409_);
                if v_isZero_2410_ == 1 {
                    leanh::lean_dec(v_x_2408_);
                    return v_isZero_2410_;
                } else {
                    v_one_2411_ = leanh::lean_unsigned_to_nat(1);
                    v_n_2412_ = lean_nat_sub(v_x_2408_, v_one_2411_);
                    leanh::lean_dec(v_x_2408_);
                    v___x_2413_ = lean_array_fget_borrowed(v_xs_2406_, v_n_2412_);
                    v___x_2414_ = lean_array_fget_borrowed(v_ys_2407_, v_n_2412_);
                    v___x_2415_ = lean_name_eq(v___x_2413_, v___x_2414_);
                    if v___x_2415_ == 0 {
                        leanh::lean_dec(v_n_2412_);
                        return v___x_2415_;
                    } else {
                        v_x_2408_ = v_n_2412_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg___boxed(
    mut v_xs_2417_: *mut leanh::LeanObject,
    mut v_ys_2418_: *mut leanh::LeanObject,
    mut v_x_2419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2420_: u8 = 0;
    let mut v_r_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2420_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(v_xs_2417_, v_ys_2418_, v_x_2419_);
    leanh::lean_dec_ref(v_ys_2418_);
    leanh::lean_dec_ref(v_xs_2417_);
    v_r_2421_ = leanh::lean_box((v_res_2420_) as usize);
    return v_r_2421_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(
    mut v_x_2422_: *mut leanh::LeanObject,
    mut v_x_2423_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_indName_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isPrivate_2426_: u8 = 0;
    let mut v_indName_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isPrivate_2429_: u8 = 0;
    let mut v___x_2430_: u8 = 0;
    v_indName_2424_ = leanh::lean_ctor_get(v_x_2422_, 0);
    v_ctors_2425_ = leanh::lean_ctor_get(v_x_2422_, 1);
    v_isPrivate_2426_ = leanh::lean_ctor_get_uint8(
        v_x_2422_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    v_indName_2427_ = leanh::lean_ctor_get(v_x_2423_, 0);
    v_ctors_2428_ = leanh::lean_ctor_get(v_x_2423_, 1);
    v_isPrivate_2429_ = leanh::lean_ctor_get_uint8(
        v_x_2423_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    v___x_2430_ = lean_name_eq(v_indName_2424_, v_indName_2427_);
    if v___x_2430_ == 0 {
        return v___x_2430_;
    } else {
        let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2433_: u8 = 0;
        v___x_2431_ = lean_array_get_size(v_ctors_2425_);
        v___x_2432_ = lean_array_get_size(v_ctors_2428_);
        v___x_2433_ = lean_nat_dec_eq(v___x_2431_, v___x_2432_);
        if v___x_2433_ == 0 {
            return v___x_2433_;
        } else {
            let mut v___x_2434_: u8 = 0;
            v___x_2434_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(v_ctors_2425_, v_ctors_2428_, v___x_2431_);
            if v___x_2434_ == 0 {
                return v___x_2434_;
            } else {
                if v_isPrivate_2426_ == 0 {
                    if v_isPrivate_2429_ == 0 {
                        return v___x_2434_;
                    } else {
                        return v_isPrivate_2426_;
                    }
                } else {
                    return v_isPrivate_2429_;
                }
            }
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq___boxed(
    mut v_x_2435_: *mut leanh::LeanObject,
    mut v_x_2436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2437_: u8 = 0;
    let mut v_r_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2437_ =
        l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(
            v_x_2435_, v_x_2436_,
        );
    leanh::lean_dec_ref(v_x_2436_);
    leanh::lean_dec_ref(v_x_2435_);
    v_r_2438_ = leanh::lean_box((v_res_2437_) as usize);
    return v_r_2438_;
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0(
    mut v_xs_2439_: *mut leanh::LeanObject,
    mut v_ys_2440_: *mut leanh::LeanObject,
    mut v_hsz_2441_: *mut leanh::LeanObject,
    mut v_x_2442_: *mut leanh::LeanObject,
    mut v_x_2443_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2444_: u8 = 0;
    v___x_2444_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(v_xs_2439_, v_ys_2440_, v_x_2442_);
    return v___x_2444_;
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___boxed(
    mut v_xs_2445_: *mut leanh::LeanObject,
    mut v_ys_2446_: *mut leanh::LeanObject,
    mut v_hsz_2447_: *mut leanh::LeanObject,
    mut v_x_2448_: *mut leanh::LeanObject,
    mut v_x_2449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2450_: u8 = 0;
    let mut v_r_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2450_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0(v_xs_2445_, v_ys_2446_, v_hsz_2447_, v_x_2448_, v_x_2449_);
    leanh::lean_dec_ref(v_ys_2446_);
    leanh::lean_dec_ref(v_xs_2445_);
    v_r_2451_ = leanh::lean_box((v_res_2450_) as usize);
    return v_r_2451_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___closed__0()
-> u64 {
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: u64 = 0;
    v___x_2454_ = leanh::lean_unsigned_to_nat(1723);
    v___x_2455_ = lean_uint64_of_nat(v___x_2454_);
    return v___x_2455_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(
    mut v_as_2456_: *mut leanh::LeanObject,
    mut v_i_2457_: usize,
    mut v_stop_2458_: usize,
    mut v_b_2459_: u64,
) -> u64 {
    let mut v___y_2461_: u64 = 0;
    let mut v___x_2462_: u64 = 0;
    let mut v___x_2463_: usize = 0;
    let mut v___x_2464_: usize = 0;
    let mut v___x_2466_: u8 = 0;
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: u64 = 0;
    let mut v_hash_2469_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2466_ = lean_usize_dec_eq(v_i_2457_, v_stop_2458_);
                if v___x_2466_ == 0 {
                    v___x_2467_ = lean_array_uget_borrowed(v_as_2456_, v_i_2457_);
                    if leanh::lean_obj_tag(v___x_2467_) == 0 {
                        v___x_2468_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___closed__0);
                        v___y_2461_ = v___x_2468_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_2469_ = leanh::lean_ctor_get_uint64(
                            v___x_2467_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2461_ = v_hash_2469_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_2459_;
                }
            }
            1 => {
                v___x_2462_ = lean_uint64_mix_hash(v_b_2459_, v___y_2461_);
                v___x_2463_ = 1usize;
                v___x_2464_ = lean_usize_add(v_i_2457_, v___x_2463_);
                v_i_2457_ = v___x_2464_;
                v_b_2459_ = v___x_2462_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___boxed(
    mut v_as_2470_: *mut leanh::LeanObject,
    mut v_i_2471_: *mut leanh::LeanObject,
    mut v_stop_2472_: *mut leanh::LeanObject,
    mut v_b_2473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2474_: usize = 0;
    let mut v_stop_boxed_2475_: usize = 0;
    let mut v_b_boxed_2476_: u64 = 0;
    let mut v_res_2477_: u64 = 0;
    let mut v_r_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2474_ = leanh::lean_unbox_usize(v_i_2471_);
    leanh::lean_dec(v_i_2471_);
    v_stop_boxed_2475_ = leanh::lean_unbox_usize(v_stop_2472_);
    leanh::lean_dec(v_stop_2472_);
    v_b_boxed_2476_ = leanh::lean_unbox_uint64(v_b_2473_);
    leanh::lean_dec_ref(v_b_2473_);
    v_res_2477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(v_as_2470_, v_i_boxed_2474_, v_stop_boxed_2475_, v_b_boxed_2476_);
    leanh::lean_dec_ref(v_as_2470_);
    v_r_2478_ = leanh::lean_box_uint64(v_res_2477_);
    return v_r_2478_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(
    mut v_x_2479_: *mut leanh::LeanObject,
) -> u64 {
    let mut v_indName_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isPrivate_2482_: u8 = 0;
    let mut v___y_2484_: u64 = 0;
    let mut v___y_2485_: u64 = 0;
    let mut v___x_2486_: u64 = 0;
    let mut v___x_2487_: u64 = 0;
    let mut v___x_2488_: u64 = 0;
    let mut v___x_2489_: u64 = 0;
    let mut v___x_2490_: u64 = 0;
    let mut v___x_2491_: u64 = 0;
    let mut v___y_2493_: u64 = 0;
    let mut v___x_2494_: u64 = 0;
    let mut v___x_2495_: u64 = 0;
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: u8 = 0;
    let mut v___x_2499_: u8 = 0;
    let mut v___x_2500_: usize = 0;
    let mut v___x_2501_: usize = 0;
    let mut v___x_2502_: u64 = 0;
    let mut v___x_2503_: usize = 0;
    let mut v___x_2504_: usize = 0;
    let mut v___x_2505_: u64 = 0;
    let mut v___x_2506_: u64 = 0;
    let mut v_hash_2507_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_indName_2480_ = leanh::lean_ctor_get(v_x_2479_, 0);
                v_ctors_2481_ = leanh::lean_ctor_get(v_x_2479_, 1);
                v_isPrivate_2482_ = leanh::lean_ctor_get_uint8(
                    v_x_2479_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v___x_2491_ = 0u64;
                if leanh::lean_obj_tag(v_indName_2480_) == 0 {
                    v___x_2506_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___closed__0);
                    v___y_2493_ = v___x_2506_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2507_ = leanh::lean_ctor_get_uint64(
                        v_indName_2480_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2493_ = v_hash_2507_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2486_ = lean_uint64_mix_hash(v___y_2484_, v___y_2485_);
                if v_isPrivate_2482_ == 0 {
                    v___x_2487_ = 13u64;
                    v___x_2488_ = lean_uint64_mix_hash(v___x_2486_, v___x_2487_);
                    return v___x_2488_;
                } else {
                    v___x_2489_ = 11u64;
                    v___x_2490_ = lean_uint64_mix_hash(v___x_2486_, v___x_2489_);
                    return v___x_2490_;
                }
            }
            2 => {
                v___x_2494_ = lean_uint64_mix_hash(v___x_2491_, v___y_2493_);
                v___x_2495_ = 7u64;
                v___x_2496_ = leanh::lean_unsigned_to_nat(0);
                v___x_2497_ = lean_array_get_size(v_ctors_2481_);
                v___x_2498_ = lean_nat_dec_lt(v___x_2496_, v___x_2497_);
                if v___x_2498_ == 0 {
                    v___y_2484_ = v___x_2494_;
                    v___y_2485_ = v___x_2495_;
                    state = 1;
                    continue;
                } else {
                    v___x_2499_ = lean_nat_dec_le(v___x_2497_, v___x_2497_);
                    if v___x_2499_ == 0 {
                        if v___x_2498_ == 0 {
                            v___y_2484_ = v___x_2494_;
                            v___y_2485_ = v___x_2495_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2500_ = 0usize;
                            v___x_2501_ = lean_usize_of_nat(v___x_2497_);
                            v___x_2502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(v_ctors_2481_, v___x_2500_, v___x_2501_, v___x_2495_);
                            v___y_2484_ = v___x_2494_;
                            v___y_2485_ = v___x_2502_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2503_ = 0usize;
                        v___x_2504_ = lean_usize_of_nat(v___x_2497_);
                        v___x_2505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(v_ctors_2481_, v___x_2503_, v___x_2504_, v___x_2495_);
                        v___y_2484_ = v___x_2494_;
                        v___y_2485_ = v___x_2505_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash___boxed(
    mut v_x_2508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2509_: u64 = 0;
    let mut v_r_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2509_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_2508_);
    leanh::lean_dec_ref(v_x_2508_);
    v_r_2510_ = leanh::lean_box_uint64(v_res_2509_);
    return v_r_2510_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_(
    mut v___x_2513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2515_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2515_, 0, v___x_2513_);
    return v___x_2515_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2____boxed(
    mut v___x_2516_: *mut leanh::LeanObject,
    mut v___y_2517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2518_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_(v___x_2516_);
    return v_res_2518_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2519_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2519_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2520_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_);
    v___x_2521_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2521_, 0, v___x_2520_);
    return v___x_2521_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2522_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_);
    v___f_2523_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_2523_, 0, v___x_2522_);
    return v___f_2523_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2525_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_);
    v___x_2526_ = leanh::lean_box(0);
    v___x_2527_ = leanh::lean_box(1);
    v___x_2528_ = l_Lean_registerEnvExtension___redArg(v___f_2525_, v___x_2526_, v___x_2527_);
    return v___x_2528_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2____boxed(
    mut v_a_2529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2530_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_();
    return v_res_2530_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_(
    mut v_env_2539_: *mut leanh::LeanObject,
    mut v_n_2540_: *mut leanh::LeanObject,
    mut v_x_2541_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2542_: u8 = 0;
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: u8 = 0;
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2542_ = 1;
    v___x_2543_ = l_Lean_Environment_setExporting(v_env_2539_, v___x_2542_);
    v___x_2544_ = 0;
    v___x_2545_ = l_Lean_Environment_find_x3f(v___x_2543_, v_n_2540_, v___x_2544_);
    if leanh::lean_obj_tag(v___x_2545_) == 0 {
        return v___x_2544_;
    } else {
        let mut v_val_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2547_: u8 = 0;
        v_val_2546_ = leanh::lean_ctor_get(v___x_2545_, 0);
        leanh::lean_inc(v_val_2546_);
        leanh::lean_dec_ref_known(v___x_2545_, 1);
        v___x_2547_ = l_Lean_ConstantInfo_hasValue(v_val_2546_, v___x_2544_);
        leanh::lean_dec(v_val_2546_);
        return v___x_2547_;
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2____boxed(
    mut v_env_2548_: *mut leanh::LeanObject,
    mut v_n_2549_: *mut leanh::LeanObject,
    mut v_x_2550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2551_: u8 = 0;
    let mut v_r_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2551_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_(v_env_2548_, v_n_2549_, v_x_2550_);
    leanh::lean_dec_ref(v_x_2550_);
    v_r_2552_ = leanh::lean_box((v_res_2551_) as usize);
    return v_r_2552_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0_spec__0(
    mut v_init_2553_: *mut leanh::LeanObject,
    mut v_x_2554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2554_) == 0 {
                    v_k_2555_ = leanh::lean_ctor_get(v_x_2554_, 1);
                    v_v_2556_ = leanh::lean_ctor_get(v_x_2554_, 2);
                    v_l_2557_ = leanh::lean_ctor_get(v_x_2554_, 3);
                    v_r_2558_ = leanh::lean_ctor_get(v_x_2554_, 4);
                    v___x_2559_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0_spec__0(v_init_2553_, v_l_2557_);
                    leanh::lean_inc(v_v_2556_);
                    leanh::lean_inc(v_k_2555_);
                    v___x_2560_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2560_, 0, v_k_2555_);
                    leanh::lean_ctor_set(v___x_2560_, 1, v_v_2556_);
                    v___x_2561_ = lean_array_push(v___x_2559_, v___x_2560_);
                    v_init_2553_ = v___x_2561_;
                    v_x_2554_ = v_r_2558_;
                    state = 0;
                    continue;
                } else {
                    return v_init_2553_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_init_2563_: *mut leanh::LeanObject,
    mut v_x_2564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2565_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0_spec__0(v_init_2563_, v_x_2564_);
    leanh::lean_dec(v_x_2564_);
    return v_res_2565_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_(
    mut v_env_2568_: *mut leanh::LeanObject,
    mut v_s_2569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exported_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2570_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___f_2570_, 0, v_env_2568_);
    v___x_2571_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_;
    v_all_2572_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0_spec__0(v___x_2571_, v_s_2569_);
    v___x_2573_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(
        v___f_2570_,
        v_s_2569_,
    );
    v_exported_2574_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0_spec__0(v___x_2571_, v___x_2573_);
    leanh::lean_dec(v___x_2573_);
    leanh::lean_inc_ref(v_exported_2574_);
    v___x_2575_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2575_, 0, v_exported_2574_);
    leanh::lean_ctor_set(v___x_2575_, 1, v_exported_2574_);
    leanh::lean_ctor_set(v___x_2575_, 2, v_all_2572_);
    return v___x_2575_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2613_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_;
    v___x_2614_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_;
    v___x_2615_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_;
    v___x_2616_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_2614_, v___x_2615_, v___f_2613_);
    return v___x_2616_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2____boxed(
    mut v_a_2617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2618_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_();
    return v_res_2618_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0(
    mut v_init_2619_: *mut leanh::LeanObject,
    mut v_t_2620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2621_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0_spec__0(v_init_2619_, v_t_2620_);
    return v___x_2621_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0___boxed(
    mut v_init_2622_: *mut leanh::LeanObject,
    mut v_t_2623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2624_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2__spec__0(v_init_2622_, v_t_2623_);
    leanh::lean_dec(v_t_2623_);
    return v_res_2624_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(
    mut v_kind_2625_: *mut leanh::LeanObject,
    mut v___y_2626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2646_: u8 = 0;
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2652_: u8 = 0;
    let mut v_unused_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2628_ = lean_st_ref_get(v___y_2626_);
                v_auxDeclNGen_2629_ = leanh::lean_ctor_get(v___x_2628_, 3);
                leanh::lean_inc_ref(v_auxDeclNGen_2629_);
                leanh::lean_dec(v___x_2628_);
                v___x_2630_ = lean_st_ref_get(v___y_2626_);
                v_env_2631_ = leanh::lean_ctor_get(v___x_2630_, 0);
                leanh::lean_inc_ref(v_env_2631_);
                leanh::lean_dec(v___x_2630_);
                v___x_2632_ = l_Lean_DeclNameGenerator_mkUniqueName(
                    v_env_2631_,
                    v_auxDeclNGen_2629_,
                    v_kind_2625_,
                );
                v_fst_2633_ = leanh::lean_ctor_get(v___x_2632_, 0);
                leanh::lean_inc(v_fst_2633_);
                v_snd_2634_ = leanh::lean_ctor_get(v___x_2632_, 1);
                leanh::lean_inc(v_snd_2634_);
                leanh::lean_dec_ref(v___x_2632_);
                v___x_2635_ = lean_st_ref_take(v___y_2626_);
                v_env_2636_ = leanh::lean_ctor_get(v___x_2635_, 0);
                v_nextMacroScope_2637_ = leanh::lean_ctor_get(v___x_2635_, 1);
                v_ngen_2638_ = leanh::lean_ctor_get(v___x_2635_, 2);
                v_traceState_2639_ = leanh::lean_ctor_get(v___x_2635_, 4);
                v_cache_2640_ = leanh::lean_ctor_get(v___x_2635_, 5);
                v_messages_2641_ = leanh::lean_ctor_get(v___x_2635_, 6);
                v_infoState_2642_ = leanh::lean_ctor_get(v___x_2635_, 7);
                v_snapshotTasks_2643_ = leanh::lean_ctor_get(v___x_2635_, 8);
                v_isSharedCheck_2652_ = (!leanh::lean_is_exclusive(v___x_2635_)) as u8;
                if v_isSharedCheck_2652_ == 0 {
                    v_unused_2653_ = leanh::lean_ctor_get(v___x_2635_, 3);
                    leanh::lean_dec(v_unused_2653_);
                    v___x_2645_ = v___x_2635_;
                    v_isShared_2646_ = v_isSharedCheck_2652_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2643_);
                    leanh::lean_inc(v_infoState_2642_);
                    leanh::lean_inc(v_messages_2641_);
                    leanh::lean_inc(v_cache_2640_);
                    leanh::lean_inc(v_traceState_2639_);
                    leanh::lean_inc(v_ngen_2638_);
                    leanh::lean_inc(v_nextMacroScope_2637_);
                    leanh::lean_inc(v_env_2636_);
                    leanh::lean_dec(v___x_2635_);
                    v___x_2645_ = leanh::lean_box(0);
                    v_isShared_2646_ = v_isSharedCheck_2652_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2646_ == 0 {
                    leanh::lean_ctor_set(v___x_2645_, 3, v_snd_2634_);
                    v___x_2648_ = v___x_2645_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2651_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_env_2636_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 1, v_nextMacroScope_2637_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 2, v_ngen_2638_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 3, v_snd_2634_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 4, v_traceState_2639_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 5, v_cache_2640_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 6, v_messages_2641_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 7, v_infoState_2642_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 8, v_snapshotTasks_2643_);
                    v___x_2648_ = v_reuseFailAlloc_2651_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2649_ = lean_st_ref_set(v___y_2626_, v___x_2648_);
                v___x_2650_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2650_, 0, v_fst_2633_);
                return v___x_2650_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg___boxed(
    mut v_kind_2654_: *mut leanh::LeanObject,
    mut v___y_2655_: *mut leanh::LeanObject,
    mut v___y_2656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2657_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(
        v_kind_2654_,
        v___y_2655_,
    );
    leanh::lean_dec(v___y_2655_);
    return v_res_2657_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2(
    mut v_kind_2658_: *mut leanh::LeanObject,
    mut v___y_2659_: *mut leanh::LeanObject,
    mut v___y_2660_: *mut leanh::LeanObject,
    mut v___y_2661_: *mut leanh::LeanObject,
    mut v___y_2662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2664_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(
        v_kind_2658_,
        v___y_2662_,
    );
    return v___x_2664_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___boxed(
    mut v_kind_2665_: *mut leanh::LeanObject,
    mut v___y_2666_: *mut leanh::LeanObject,
    mut v___y_2667_: *mut leanh::LeanObject,
    mut v___y_2668_: *mut leanh::LeanObject,
    mut v___y_2669_: *mut leanh::LeanObject,
    mut v___y_2670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2671_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2(
        v_kind_2665_,
        v___y_2666_,
        v___y_2667_,
        v___y_2668_,
        v___y_2669_,
    );
    leanh::lean_dec(v___y_2669_);
    leanh::lean_dec_ref(v___y_2668_);
    leanh::lean_dec(v___y_2667_);
    leanh::lean_dec_ref(v___y_2666_);
    return v_res_2671_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___lam__0(
    mut v_k_2672_: *mut leanh::LeanObject,
    mut v_b_2673_: *mut leanh::LeanObject,
    mut v_c_2674_: *mut leanh::LeanObject,
    mut v___y_2675_: *mut leanh::LeanObject,
    mut v___y_2676_: *mut leanh::LeanObject,
    mut v___y_2677_: *mut leanh::LeanObject,
    mut v___y_2678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_2678_);
    leanh::lean_inc_ref(v___y_2677_);
    leanh::lean_inc(v___y_2676_);
    leanh::lean_inc_ref(v___y_2675_);
    v___x_2680_ = leanh::lean_apply_7(
        v_k_2672_,
        v_b_2673_,
        v_c_2674_,
        v___y_2675_,
        v___y_2676_,
        v___y_2677_,
        v___y_2678_,
        leanh::lean_box(0),
    );
    return v___x_2680_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___lam__0___boxed(
    mut v_k_2681_: *mut leanh::LeanObject,
    mut v_b_2682_: *mut leanh::LeanObject,
    mut v_c_2683_: *mut leanh::LeanObject,
    mut v___y_2684_: *mut leanh::LeanObject,
    mut v___y_2685_: *mut leanh::LeanObject,
    mut v___y_2686_: *mut leanh::LeanObject,
    mut v___y_2687_: *mut leanh::LeanObject,
    mut v___y_2688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2689_ =
        l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___lam__0(
            v_k_2681_,
            v_b_2682_,
            v_c_2683_,
            v___y_2684_,
            v___y_2685_,
            v___y_2686_,
            v___y_2687_,
        );
    leanh::lean_dec(v___y_2687_);
    leanh::lean_dec_ref(v___y_2686_);
    leanh::lean_dec(v___y_2685_);
    leanh::lean_dec_ref(v___y_2684_);
    return v_res_2689_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(
    mut v_type_2690_: *mut leanh::LeanObject,
    mut v_k_2691_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2692_: u8,
    mut v___y_2693_: *mut leanh::LeanObject,
    mut v___y_2694_: *mut leanh::LeanObject,
    mut v___y_2695_: *mut leanh::LeanObject,
    mut v___y_2696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: u8 = 0;
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2705_: u8 = 0;
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2709_: u8 = 0;
    let mut v_a_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2713_: u8 = 0;
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2717_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2698_ = leanh::lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_2698_, 0, v_k_2691_);
                v___x_2699_ = 0;
                v___x_2700_ = leanh::lean_box(0);
                v___x_2701_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        leanh::lean_box(0),
                        v___x_2699_,
                        v___x_2700_,
                        v_type_2690_,
                        v___f_2698_,
                        v_cleanupAnnotations_2692_,
                        v___x_2699_,
                        v___y_2693_,
                        v___y_2694_,
                        v___y_2695_,
                        v___y_2696_,
                    );
                if leanh::lean_obj_tag(v___x_2701_) == 0 {
                    v_a_2702_ = leanh::lean_ctor_get(v___x_2701_, 0);
                    v_isSharedCheck_2709_ = (!leanh::lean_is_exclusive(v___x_2701_)) as u8;
                    if v_isSharedCheck_2709_ == 0 {
                        v___x_2704_ = v___x_2701_;
                        v_isShared_2705_ = v_isSharedCheck_2709_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2702_);
                        leanh::lean_dec(v___x_2701_);
                        v___x_2704_ = leanh::lean_box(0);
                        v_isShared_2705_ = v_isSharedCheck_2709_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2710_ = leanh::lean_ctor_get(v___x_2701_, 0);
                    v_isSharedCheck_2717_ = (!leanh::lean_is_exclusive(v___x_2701_)) as u8;
                    if v_isSharedCheck_2717_ == 0 {
                        v___x_2712_ = v___x_2701_;
                        v_isShared_2713_ = v_isSharedCheck_2717_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2710_);
                        leanh::lean_dec(v___x_2701_);
                        v___x_2712_ = leanh::lean_box(0);
                        v_isShared_2713_ = v_isSharedCheck_2717_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2705_ == 0 {
                    v___x_2707_ = v___x_2704_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2708_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
                    v___x_2707_ = v_reuseFailAlloc_2708_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2707_;
            }
            3 => {
                if v_isShared_2713_ == 0 {
                    v___x_2715_ = v___x_2712_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2716_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
                    v___x_2715_ = v_reuseFailAlloc_2716_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2715_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg___boxed(
    mut v_type_2718_: *mut leanh::LeanObject,
    mut v_k_2719_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2720_: *mut leanh::LeanObject,
    mut v___y_2721_: *mut leanh::LeanObject,
    mut v___y_2722_: *mut leanh::LeanObject,
    mut v___y_2723_: *mut leanh::LeanObject,
    mut v___y_2724_: *mut leanh::LeanObject,
    mut v___y_2725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2726_: u8 = 0;
    let mut v_res_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2726_ = (leanh::lean_unbox(v_cleanupAnnotations_2720_) as u8);
    v_res_2727_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(
        v_type_2718_,
        v_k_2719_,
        v_cleanupAnnotations_boxed_2726_,
        v___y_2721_,
        v___y_2722_,
        v___y_2723_,
        v___y_2724_,
    );
    leanh::lean_dec(v___y_2724_);
    leanh::lean_dec_ref(v___y_2723_);
    leanh::lean_dec(v___y_2722_);
    leanh::lean_dec_ref(v___y_2721_);
    return v_res_2727_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11(
    mut v_00_u03b1_2728_: *mut leanh::LeanObject,
    mut v_type_2729_: *mut leanh::LeanObject,
    mut v_k_2730_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2731_: u8,
    mut v___y_2732_: *mut leanh::LeanObject,
    mut v___y_2733_: *mut leanh::LeanObject,
    mut v___y_2734_: *mut leanh::LeanObject,
    mut v___y_2735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2737_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(
        v_type_2729_,
        v_k_2730_,
        v_cleanupAnnotations_2731_,
        v___y_2732_,
        v___y_2733_,
        v___y_2734_,
        v___y_2735_,
    );
    return v___x_2737_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___boxed(
    mut v_00_u03b1_2738_: *mut leanh::LeanObject,
    mut v_type_2739_: *mut leanh::LeanObject,
    mut v_k_2740_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2741_: *mut leanh::LeanObject,
    mut v___y_2742_: *mut leanh::LeanObject,
    mut v___y_2743_: *mut leanh::LeanObject,
    mut v___y_2744_: *mut leanh::LeanObject,
    mut v___y_2745_: *mut leanh::LeanObject,
    mut v___y_2746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2747_: u8 = 0;
    let mut v_res_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2747_ = (leanh::lean_unbox(v_cleanupAnnotations_2741_) as u8);
    v_res_2748_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11(
        v_00_u03b1_2738_,
        v_type_2739_,
        v_k_2740_,
        v_cleanupAnnotations_boxed_2747_,
        v___y_2742_,
        v___y_2743_,
        v___y_2744_,
        v___y_2745_,
    );
    leanh::lean_dec(v___y_2745_);
    leanh::lean_dec_ref(v___y_2744_);
    leanh::lean_dec(v___y_2743_);
    leanh::lean_dec_ref(v___y_2742_);
    return v_res_2748_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(
    mut v_name_2749_: *mut leanh::LeanObject,
    mut v_levelParams_2750_: *mut leanh::LeanObject,
    mut v_type_2751_: *mut leanh::LeanObject,
    mut v_value_2752_: *mut leanh::LeanObject,
    mut v_hints_2753_: *mut leanh::LeanObject,
    mut v___y_2754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2758_: u8 = 0;
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2765_: u8 = 0;
    let mut v___x_2766_: u8 = 0;
    let mut v___x_2767_: u8 = 0;
    let mut v_env_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: u8 = 0;
    let mut v___x_2770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2756_ = lean_st_ref_get(v___y_2754_);
                v_env_2768_ = leanh::lean_ctor_get(v___x_2756_, 0);
                leanh::lean_inc_ref_n(v_env_2768_, 2);
                leanh::lean_dec(v___x_2756_);
                v___x_2769_ = l_Lean_Environment_hasUnsafe(v_env_2768_, v_type_2751_);
                if v___x_2769_ == 0 {
                    v___x_2770_ = l_Lean_Environment_hasUnsafe(v_env_2768_, v_value_2752_);
                    v___y_2765_ = v___x_2770_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_env_2768_);
                    v___y_2765_ = v___x_2769_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_name_2749_);
                v___x_2759_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2759_, 0, v_name_2749_);
                leanh::lean_ctor_set(v___x_2759_, 1, v_levelParams_2750_);
                leanh::lean_ctor_set(v___x_2759_, 2, v_type_2751_);
                v___x_2760_ = leanh::lean_box(0);
                v___x_2761_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2761_, 0, v_name_2749_);
                leanh::lean_ctor_set(v___x_2761_, 1, v___x_2760_);
                v___x_2762_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_2762_, 0, v___x_2759_);
                leanh::lean_ctor_set(v___x_2762_, 1, v_value_2752_);
                leanh::lean_ctor_set(v___x_2762_, 2, v_hints_2753_);
                leanh::lean_ctor_set(v___x_2762_, 3, v___x_2761_);
                leanh::lean_ctor_set_uint8(
                    v___x_2762_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___y_2758_,
                );
                v___x_2763_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2763_, 0, v___x_2762_);
                return v___x_2763_;
            }
            2 => {
                if v___y_2765_ == 0 {
                    v___x_2766_ = 1;
                    v___y_2758_ = v___x_2766_;
                    state = 1;
                    continue;
                } else {
                    v___x_2767_ = 0;
                    v___y_2758_ = v___x_2767_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg___boxed(
    mut v_name_2771_: *mut leanh::LeanObject,
    mut v_levelParams_2772_: *mut leanh::LeanObject,
    mut v_type_2773_: *mut leanh::LeanObject,
    mut v_value_2774_: *mut leanh::LeanObject,
    mut v_hints_2775_: *mut leanh::LeanObject,
    mut v___y_2776_: *mut leanh::LeanObject,
    mut v___y_2777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2778_ =
        l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(
            v_name_2771_,
            v_levelParams_2772_,
            v_type_2773_,
            v_value_2774_,
            v_hints_2775_,
            v___y_2776_,
        );
    leanh::lean_dec(v___y_2776_);
    return v_res_2778_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14(
    mut v_name_2779_: *mut leanh::LeanObject,
    mut v_levelParams_2780_: *mut leanh::LeanObject,
    mut v_type_2781_: *mut leanh::LeanObject,
    mut v_value_2782_: *mut leanh::LeanObject,
    mut v_hints_2783_: *mut leanh::LeanObject,
    mut v___y_2784_: *mut leanh::LeanObject,
    mut v___y_2785_: *mut leanh::LeanObject,
    mut v___y_2786_: *mut leanh::LeanObject,
    mut v___y_2787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2789_ =
        l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(
            v_name_2779_,
            v_levelParams_2780_,
            v_type_2781_,
            v_value_2782_,
            v_hints_2783_,
            v___y_2787_,
        );
    return v___x_2789_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___boxed(
    mut v_name_2790_: *mut leanh::LeanObject,
    mut v_levelParams_2791_: *mut leanh::LeanObject,
    mut v_type_2792_: *mut leanh::LeanObject,
    mut v_value_2793_: *mut leanh::LeanObject,
    mut v_hints_2794_: *mut leanh::LeanObject,
    mut v___y_2795_: *mut leanh::LeanObject,
    mut v___y_2796_: *mut leanh::LeanObject,
    mut v___y_2797_: *mut leanh::LeanObject,
    mut v___y_2798_: *mut leanh::LeanObject,
    mut v___y_2799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2800_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14(
        v_name_2790_,
        v_levelParams_2791_,
        v_type_2792_,
        v_value_2793_,
        v_hints_2794_,
        v___y_2795_,
        v___y_2796_,
        v___y_2797_,
        v___y_2798_,
    );
    leanh::lean_dec(v___y_2798_);
    leanh::lean_dec_ref(v___y_2797_);
    leanh::lean_dec(v___y_2796_);
    leanh::lean_dec_ref(v___y_2795_);
    return v_res_2800_;
}
pub unsafe fn l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16(
    mut v_msg_2802_: *mut leanh::LeanObject,
    mut v___y_2803_: *mut leanh::LeanObject,
    mut v___y_2804_: *mut leanh::LeanObject,
    mut v___y_2805_: *mut leanh::LeanObject,
    mut v___y_2806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_16979__overap_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2808_ = l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16___closed__0;
    v___x_16979__overap_2809_ = lean_panic_fn_borrowed(v___f_2808_, v_msg_2802_);
    leanh::lean_inc(v___y_2806_);
    leanh::lean_inc_ref(v___y_2805_);
    leanh::lean_inc(v___y_2804_);
    leanh::lean_inc_ref(v___y_2803_);
    v___x_2810_ = leanh::lean_apply_5(
        v___x_16979__overap_2809_,
        v___y_2803_,
        v___y_2804_,
        v___y_2805_,
        v___y_2806_,
        leanh::lean_box(0),
    );
    return v___x_2810_;
}
pub unsafe fn l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16___boxed(
    mut v_msg_2811_: *mut leanh::LeanObject,
    mut v___y_2812_: *mut leanh::LeanObject,
    mut v___y_2813_: *mut leanh::LeanObject,
    mut v___y_2814_: *mut leanh::LeanObject,
    mut v___y_2815_: *mut leanh::LeanObject,
    mut v___y_2816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2817_ = l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16(
        v_msg_2811_,
        v___y_2812_,
        v___y_2813_,
        v___y_2814_,
        v___y_2815_,
    );
    leanh::lean_dec(v___y_2815_);
    leanh::lean_dec_ref(v___y_2814_);
    leanh::lean_dec(v___y_2813_);
    leanh::lean_dec_ref(v___y_2812_);
    return v_res_2817_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26___redArg(
    mut v_x_2818_: *mut leanh::LeanObject,
    mut v_x_2819_: *mut leanh::LeanObject,
    mut v_x_2820_: *mut leanh::LeanObject,
    mut v_x_2821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2826_: u8 = 0;
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: u8 = 0;
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: u8 = 0;
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2847_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2822_ = leanh::lean_ctor_get(v_x_2818_, 0);
                v_vs_2823_ = leanh::lean_ctor_get(v_x_2818_, 1);
                v_isSharedCheck_2847_ = (!leanh::lean_is_exclusive(v_x_2818_)) as u8;
                if v_isSharedCheck_2847_ == 0 {
                    v___x_2825_ = v_x_2818_;
                    v_isShared_2826_ = v_isSharedCheck_2847_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_2823_);
                    leanh::lean_inc(v_ks_2822_);
                    leanh::lean_dec(v_x_2818_);
                    v___x_2825_ = leanh::lean_box(0);
                    v_isShared_2826_ = v_isSharedCheck_2847_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2827_ = lean_array_get_size(v_ks_2822_);
                v___x_2828_ = lean_nat_dec_lt(v_x_2819_, v___x_2827_);
                if v___x_2828_ == 0 {
                    leanh::lean_dec(v_x_2819_);
                    v___x_2829_ = lean_array_push(v_ks_2822_, v_x_2820_);
                    v___x_2830_ = lean_array_push(v_vs_2823_, v_x_2821_);
                    if v_isShared_2826_ == 0 {
                        leanh::lean_ctor_set(v___x_2825_, 1, v___x_2830_);
                        leanh::lean_ctor_set(v___x_2825_, 0, v___x_2829_);
                        v___x_2832_ = v___x_2825_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2833_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2829_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2833_, 1, v___x_2830_);
                        v___x_2832_ = v_reuseFailAlloc_2833_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2834_ = lean_array_fget_borrowed(v_ks_2822_, v_x_2819_);
                    v___x_2835_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_2820_, v_k_x27_2834_);
                    if v___x_2835_ == 0 {
                        if v_isShared_2826_ == 0 {
                            v___x_2837_ = v___x_2825_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2841_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_ks_2822_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_vs_2823_);
                            v___x_2837_ = v_reuseFailAlloc_2841_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2842_ = lean_array_fset(v_ks_2822_, v_x_2819_, v_x_2820_);
                        v___x_2843_ = lean_array_fset(v_vs_2823_, v_x_2819_, v_x_2821_);
                        leanh::lean_dec(v_x_2819_);
                        if v_isShared_2826_ == 0 {
                            leanh::lean_ctor_set(v___x_2825_, 1, v___x_2843_);
                            leanh::lean_ctor_set(v___x_2825_, 0, v___x_2842_);
                            v___x_2845_ = v___x_2825_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2846_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2842_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 1, v___x_2843_);
                            v___x_2845_ = v_reuseFailAlloc_2846_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2832_;
            }
            3 => {
                v___x_2838_ = leanh::lean_unsigned_to_nat(1);
                v___x_2839_ = lean_nat_add(v_x_2819_, v___x_2838_);
                leanh::lean_dec(v_x_2819_);
                v_x_2818_ = v___x_2837_;
                v_x_2819_ = v___x_2839_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2845_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10___redArg(
    mut v_n_2848_: *mut leanh::LeanObject,
    mut v_k_2849_: *mut leanh::LeanObject,
    mut v_v_2850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2851_ = leanh::lean_unsigned_to_nat(0);
    v___x_2852_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26___redArg(v_n_2848_, v___x_2851_, v_k_2849_, v_v_2850_);
    return v___x_2852_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0()
-> usize {
    let mut v___x_2853_: usize = 0;
    let mut v___x_2854_: usize = 0;
    let mut v___x_2855_: usize = 0;
    v___x_2853_ = 5usize;
    v___x_2854_ = 1usize;
    v___x_2855_ = lean_usize_shift_left(v___x_2854_, v___x_2853_);
    return v___x_2855_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__1()
-> usize {
    let mut v___x_2856_: usize = 0;
    let mut v___x_2857_: usize = 0;
    let mut v___x_2858_: usize = 0;
    v___x_2856_ = 1usize;
    v___x_2857_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0);
    v___x_2858_ = lean_usize_sub(v___x_2857_, v___x_2856_);
    return v___x_2858_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2859_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2859_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(
    mut v_x_2860_: *mut leanh::LeanObject,
    mut v_x_2861_: usize,
    mut v_x_2862_: usize,
    mut v_x_2863_: *mut leanh::LeanObject,
    mut v_x_2864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: usize = 0;
    let mut v___x_2867_: usize = 0;
    let mut v___x_2868_: usize = 0;
    let mut v___x_2869_: usize = 0;
    let mut v_j_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: u8 = 0;
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2875_: u8 = 0;
    let mut v_v_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2889_: u8 = 0;
    let mut v___x_2890_: u8 = 0;
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2896_: u8 = 0;
    let mut v_node_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2900_: u8 = 0;
    let mut v___x_2901_: usize = 0;
    let mut v___x_2902_: usize = 0;
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2907_: u8 = 0;
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2909_: u8 = 0;
    let mut v_unused_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2915_: u8 = 0;
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2920_: u8 = 0;
    let mut v_ks_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: usize = 0;
    let mut v___x_2927_: u8 = 0;
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: u8 = 0;
    let mut v_reuseFailAlloc_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2932_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2860_) == 0 {
                    v_es_2865_ = leanh::lean_ctor_get(v_x_2860_, 0);
                    v___x_2866_ = 5usize;
                    v___x_2867_ = 1usize;
                    v___x_2868_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__1);
                    v___x_2869_ = lean_usize_land(v_x_2861_, v___x_2868_);
                    v_j_2870_ = lean_usize_to_nat(v___x_2869_);
                    v___x_2871_ = lean_array_get_size(v_es_2865_);
                    v___x_2872_ = lean_nat_dec_lt(v_j_2870_, v___x_2871_);
                    if v___x_2872_ == 0 {
                        leanh::lean_dec(v_j_2870_);
                        leanh::lean_dec(v_x_2864_);
                        leanh::lean_dec_ref(v_x_2863_);
                        return v_x_2860_;
                    } else {
                        leanh::lean_inc_ref(v_es_2865_);
                        v_isSharedCheck_2909_ = (!leanh::lean_is_exclusive(v_x_2860_)) as u8;
                        if v_isSharedCheck_2909_ == 0 {
                            v_unused_2910_ = leanh::lean_ctor_get(v_x_2860_, 0);
                            leanh::lean_dec(v_unused_2910_);
                            v___x_2874_ = v_x_2860_;
                            v_isShared_2875_ = v_isSharedCheck_2909_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_2860_);
                            v___x_2874_ = leanh::lean_box(0);
                            v_isShared_2875_ = v_isSharedCheck_2909_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2911_ = leanh::lean_ctor_get(v_x_2860_, 0);
                    v_vs_2912_ = leanh::lean_ctor_get(v_x_2860_, 1);
                    v_isSharedCheck_2932_ = (!leanh::lean_is_exclusive(v_x_2860_)) as u8;
                    if v_isSharedCheck_2932_ == 0 {
                        v___x_2914_ = v_x_2860_;
                        v_isShared_2915_ = v_isSharedCheck_2932_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2912_);
                        leanh::lean_inc(v_ks_2911_);
                        leanh::lean_dec(v_x_2860_);
                        v___x_2914_ = leanh::lean_box(0);
                        v_isShared_2915_ = v_isSharedCheck_2932_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2876_ = lean_array_fget(v_es_2865_, v_j_2870_);
                v___x_2877_ = leanh::lean_box(0);
                v_xs_x27_2878_ = lean_array_fset(v_es_2865_, v_j_2870_, v___x_2877_);
                match leanh::lean_obj_tag(v_v_2876_) {
                    0 => {
                        v_key_2885_ = leanh::lean_ctor_get(v_v_2876_, 0);
                        v_val_2886_ = leanh::lean_ctor_get(v_v_2876_, 1);
                        v_isSharedCheck_2896_ = (!leanh::lean_is_exclusive(v_v_2876_)) as u8;
                        if v_isSharedCheck_2896_ == 0 {
                            v___x_2888_ = v_v_2876_;
                            v_isShared_2889_ = v_isSharedCheck_2896_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2886_);
                            leanh::lean_inc(v_key_2885_);
                            leanh::lean_dec(v_v_2876_);
                            v___x_2888_ = leanh::lean_box(0);
                            v_isShared_2889_ = v_isSharedCheck_2896_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2897_ = leanh::lean_ctor_get(v_v_2876_, 0);
                        v_isSharedCheck_2907_ = (!leanh::lean_is_exclusive(v_v_2876_)) as u8;
                        if v_isSharedCheck_2907_ == 0 {
                            v___x_2899_ = v_v_2876_;
                            v_isShared_2900_ = v_isSharedCheck_2907_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_2897_);
                            leanh::lean_dec(v_v_2876_);
                            v___x_2899_ = leanh::lean_box(0);
                            v_isShared_2900_ = v_isSharedCheck_2907_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2908_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2908_, 0, v_x_2863_);
                        leanh::lean_ctor_set(v___x_2908_, 1, v_x_2864_);
                        v___y_2880_ = v___x_2908_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2881_ = lean_array_fset(v_xs_x27_2878_, v_j_2870_, v___y_2880_);
                leanh::lean_dec(v_j_2870_);
                if v_isShared_2875_ == 0 {
                    leanh::lean_ctor_set(v___x_2874_, 0, v___x_2881_);
                    v___x_2883_ = v___x_2874_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2884_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2881_);
                    v___x_2883_ = v_reuseFailAlloc_2884_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2883_;
            }
            4 => {
                v___x_2890_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_2863_, v_key_2885_);
                if v___x_2890_ == 0 {
                    leanh::lean_del_object(v___x_2888_);
                    v___x_2891_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2885_,
                        v_val_2886_,
                        v_x_2863_,
                        v_x_2864_,
                    );
                    v___x_2892_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2892_, 0, v___x_2891_);
                    v___y_2880_ = v___x_2892_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_2886_);
                    leanh::lean_dec(v_key_2885_);
                    if v_isShared_2889_ == 0 {
                        leanh::lean_ctor_set(v___x_2888_, 1, v_x_2864_);
                        leanh::lean_ctor_set(v___x_2888_, 0, v_x_2863_);
                        v___x_2894_ = v___x_2888_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2895_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_x_2863_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_x_2864_);
                        v___x_2894_ = v_reuseFailAlloc_2895_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2880_ = v___x_2894_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2901_ = lean_usize_shift_right(v_x_2861_, v___x_2866_);
                v___x_2902_ = lean_usize_add(v_x_2862_, v___x_2867_);
                v___x_2903_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_node_2897_, v___x_2901_, v___x_2902_, v_x_2863_, v_x_2864_);
                if v_isShared_2900_ == 0 {
                    leanh::lean_ctor_set(v___x_2899_, 0, v___x_2903_);
                    v___x_2905_ = v___x_2899_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2906_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2903_);
                    v___x_2905_ = v_reuseFailAlloc_2906_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2880_ = v___x_2905_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2915_ == 0 {
                    v___x_2917_ = v___x_2914_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2931_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_ks_2911_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_vs_2912_);
                    v___x_2917_ = v_reuseFailAlloc_2931_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2918_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10___redArg(v___x_2917_, v_x_2863_, v_x_2864_);
                v___x_2926_ = 7usize;
                v___x_2927_ = lean_usize_dec_le(v___x_2926_, v_x_2862_);
                if v___x_2927_ == 0 {
                    v___x_2928_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2918_);
                    v___x_2929_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2930_ = lean_nat_dec_lt(v___x_2928_, v___x_2929_);
                    leanh::lean_dec(v___x_2928_);
                    v___y_2920_ = v___x_2930_;
                    state = 10;
                    continue;
                } else {
                    v___y_2920_ = v___x_2927_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2920_ == 0 {
                    v_ks_2921_ = leanh::lean_ctor_get(v_newNode_2918_, 0);
                    leanh::lean_inc_ref(v_ks_2921_);
                    v_vs_2922_ = leanh::lean_ctor_get(v_newNode_2918_, 1);
                    leanh::lean_inc_ref(v_vs_2922_);
                    leanh::lean_dec_ref(v_newNode_2918_);
                    v___x_2923_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2924_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__2);
                    v___x_2925_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(v_x_2862_, v_ks_2921_, v_vs_2922_, v___x_2923_, v___x_2924_);
                    leanh::lean_dec_ref(v_vs_2922_);
                    leanh::lean_dec_ref(v_ks_2921_);
                    return v___x_2925_;
                } else {
                    return v_newNode_2918_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(
    mut v_depth_2933_: usize,
    mut v_keys_2934_: *mut leanh::LeanObject,
    mut v_vals_2935_: *mut leanh::LeanObject,
    mut v_i_2936_: *mut leanh::LeanObject,
    mut v_entries_2937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: u8 = 0;
    let mut v_k_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: u64 = 0;
    let mut v_h_2943_: usize = 0;
    let mut v___x_2944_: usize = 0;
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: usize = 0;
    let mut v___x_2947_: usize = 0;
    let mut v___x_2948_: usize = 0;
    let mut v_h_2949_: usize = 0;
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2938_ = lean_array_get_size(v_keys_2934_);
                v___x_2939_ = lean_nat_dec_lt(v_i_2936_, v___x_2938_);
                if v___x_2939_ == 0 {
                    leanh::lean_dec(v_i_2936_);
                    return v_entries_2937_;
                } else {
                    v_k_2940_ = lean_array_fget_borrowed(v_keys_2934_, v_i_2936_);
                    v_v_2941_ = lean_array_fget_borrowed(v_vals_2935_, v_i_2936_);
                    v___x_2942_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_k_2940_);
                    v_h_2943_ = lean_uint64_to_usize(v___x_2942_);
                    v___x_2944_ = 5usize;
                    v___x_2945_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2946_ = 1usize;
                    v___x_2947_ = lean_usize_sub(v_depth_2933_, v___x_2946_);
                    v___x_2948_ = lean_usize_mul(v___x_2944_, v___x_2947_);
                    v_h_2949_ = lean_usize_shift_right(v_h_2943_, v___x_2948_);
                    v___x_2950_ = lean_nat_add(v_i_2936_, v___x_2945_);
                    leanh::lean_dec(v_i_2936_);
                    leanh::lean_inc(v_v_2941_);
                    leanh::lean_inc(v_k_2940_);
                    v___x_2951_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_entries_2937_, v_h_2949_, v_depth_2933_, v_k_2940_, v_v_2941_);
                    v_i_2936_ = v___x_2950_;
                    v_entries_2937_ = v___x_2951_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg___boxed(
    mut v_depth_2953_: *mut leanh::LeanObject,
    mut v_keys_2954_: *mut leanh::LeanObject,
    mut v_vals_2955_: *mut leanh::LeanObject,
    mut v_i_2956_: *mut leanh::LeanObject,
    mut v_entries_2957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2958_: usize = 0;
    let mut v_res_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2958_ = leanh::lean_unbox_usize(v_depth_2953_);
    leanh::lean_dec(v_depth_2953_);
    v_res_2959_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(v_depth_boxed_2958_, v_keys_2954_, v_vals_2955_, v_i_2956_, v_entries_2957_);
    leanh::lean_dec_ref(v_vals_2955_);
    leanh::lean_dec_ref(v_keys_2954_);
    return v_res_2959_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___boxed(
    mut v_x_2960_: *mut leanh::LeanObject,
    mut v_x_2961_: *mut leanh::LeanObject,
    mut v_x_2962_: *mut leanh::LeanObject,
    mut v_x_2963_: *mut leanh::LeanObject,
    mut v_x_2964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_21156__boxed_2965_: usize = 0;
    let mut v_x_21157__boxed_2966_: usize = 0;
    let mut v_res_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_21156__boxed_2965_ = leanh::lean_unbox_usize(v_x_2961_);
    leanh::lean_dec(v_x_2961_);
    v_x_21157__boxed_2966_ = leanh::lean_unbox_usize(v_x_2962_);
    leanh::lean_dec(v_x_2962_);
    v_res_2967_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_2960_, v_x_21156__boxed_2965_, v_x_21157__boxed_2966_, v_x_2963_, v_x_2964_);
    return v_res_2967_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(
    mut v_x_2968_: *mut leanh::LeanObject,
    mut v_x_2969_: *mut leanh::LeanObject,
    mut v_x_2970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2971_: u64 = 0;
    let mut v___x_2972_: usize = 0;
    let mut v___x_2973_: usize = 0;
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2971_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_2969_);
    v___x_2972_ = lean_uint64_to_usize(v___x_2971_);
    v___x_2973_ = 1usize;
    v___x_2974_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_2968_, v___x_2972_, v___x_2973_, v_x_2969_, v_x_2970_);
    return v___x_2974_;
}
pub unsafe fn l_Lean_Meta_mkSparseCasesOn___lam__0(
    mut v___x_2975_: *mut leanh::LeanObject,
    mut v_a_2976_: *mut leanh::LeanObject,
    mut v_s_2977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2978_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(
            v_s_2977_,
            v___x_2975_,
            v_a_2976_,
        );
    return v___x_2978_;
}
pub unsafe fn l_Lean_Meta_mkSparseCasesOn___lam__1(
    mut v___x_2979_: *mut leanh::LeanObject,
    mut v___x_2980_: *mut leanh::LeanObject,
    mut v___x_2981_: *mut leanh::LeanObject,
    mut v_h_2982_: *mut leanh::LeanObject,
    mut v___y_2983_: *mut leanh::LeanObject,
    mut v___y_2984_: *mut leanh::LeanObject,
    mut v___y_2985_: *mut leanh::LeanObject,
    mut v___y_2986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: u8 = 0;
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: u8 = 0;
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2988_ = lean_array_push(v___x_2979_, v_h_2982_);
    v___x_2989_ = l_Lean_mkAppN(v___x_2980_, v___x_2981_);
    v___x_2990_ = 0;
    v___x_2991_ = 1;
    v___x_2992_ = 1;
    v___x_2993_ = l_Lean_Meta_mkForallFVars(
        v___x_2988_,
        v___x_2989_,
        v___x_2990_,
        v___x_2991_,
        v___x_2991_,
        v___x_2992_,
        v___y_2983_,
        v___y_2984_,
        v___y_2985_,
        v___y_2986_,
    );
    leanh::lean_dec_ref(v___x_2988_);
    return v___x_2993_;
}
pub unsafe fn l_Lean_Meta_mkSparseCasesOn___lam__1___boxed(
    mut v___x_2994_: *mut leanh::LeanObject,
    mut v___x_2995_: *mut leanh::LeanObject,
    mut v___x_2996_: *mut leanh::LeanObject,
    mut v_h_2997_: *mut leanh::LeanObject,
    mut v___y_2998_: *mut leanh::LeanObject,
    mut v___y_2999_: *mut leanh::LeanObject,
    mut v___y_3000_: *mut leanh::LeanObject,
    mut v___y_3001_: *mut leanh::LeanObject,
    mut v___y_3002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3003_ = l_Lean_Meta_mkSparseCasesOn___lam__1(
        v___x_2994_,
        v___x_2995_,
        v___x_2996_,
        v_h_2997_,
        v___y_2998_,
        v___y_2999_,
        v___y_3000_,
        v___y_3001_,
    );
    leanh::lean_dec(v___y_3001_);
    leanh::lean_dec_ref(v___y_3000_);
    leanh::lean_dec(v___y_2999_);
    leanh::lean_dec_ref(v___y_2998_);
    leanh::lean_dec_ref(v___x_2996_);
    return v_res_3003_;
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3004_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_3004_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(
    mut v_msg_3009_: *mut leanh::LeanObject,
    mut v___y_3010_: *mut leanh::LeanObject,
    mut v___y_3011_: *mut leanh::LeanObject,
    mut v___y_3012_: *mut leanh::LeanObject,
    mut v___y_3013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3020_: u8 = 0;
    let mut v_toFunctor_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3027_: u8 = 0;
    let mut v___f_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3044_: u8 = 0;
    let mut v_toFunctor_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3051_: u8 = 0;
    let mut v___f_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_17258__overap_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3070_: u8 = 0;
    let mut v_unused_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3072_: u8 = 0;
    let mut v_unused_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3076_: u8 = 0;
    let mut v_unused_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3078_: u8 = 0;
    let mut v_unused_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3015_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0);
                v___x_3016_ = l_StateRefT_x27_instMonad___redArg(v___x_3015_);
                v_toApplicative_3017_ = leanh::lean_ctor_get(v___x_3016_, 0);
                v_isSharedCheck_3078_ = (!leanh::lean_is_exclusive(v___x_3016_)) as u8;
                if v_isSharedCheck_3078_ == 0 {
                    v_unused_3079_ = leanh::lean_ctor_get(v___x_3016_, 1);
                    leanh::lean_dec(v_unused_3079_);
                    v___x_3019_ = v___x_3016_;
                    v_isShared_3020_ = v_isSharedCheck_3078_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_3017_);
                    leanh::lean_dec(v___x_3016_);
                    v___x_3019_ = leanh::lean_box(0);
                    v_isShared_3020_ = v_isSharedCheck_3078_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3021_ = leanh::lean_ctor_get(v_toApplicative_3017_, 0);
                v_toSeq_3022_ = leanh::lean_ctor_get(v_toApplicative_3017_, 2);
                v_toSeqLeft_3023_ = leanh::lean_ctor_get(v_toApplicative_3017_, 3);
                v_toSeqRight_3024_ = leanh::lean_ctor_get(v_toApplicative_3017_, 4);
                v_isSharedCheck_3076_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_3017_)) as u8;
                if v_isSharedCheck_3076_ == 0 {
                    v_unused_3077_ = leanh::lean_ctor_get(v_toApplicative_3017_, 1);
                    leanh::lean_dec(v_unused_3077_);
                    v___x_3026_ = v_toApplicative_3017_;
                    v_isShared_3027_ = v_isSharedCheck_3076_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_3024_);
                    leanh::lean_inc(v_toSeqLeft_3023_);
                    leanh::lean_inc(v_toSeq_3022_);
                    leanh::lean_inc(v_toFunctor_3021_);
                    leanh::lean_dec(v_toApplicative_3017_);
                    v___x_3026_ = leanh::lean_box(0);
                    v_isShared_3027_ = v_isSharedCheck_3076_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3028_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1;
                v___f_3029_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2;
                leanh::lean_inc_ref(v_toFunctor_3021_);
                v___f_3030_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3030_, 0, v_toFunctor_3021_);
                v___f_3031_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3031_, 0, v_toFunctor_3021_);
                v___x_3032_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3032_, 0, v___f_3030_);
                leanh::lean_ctor_set(v___x_3032_, 1, v___f_3031_);
                v___f_3033_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3033_, 0, v_toSeqRight_3024_);
                v___f_3034_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3034_, 0, v_toSeqLeft_3023_);
                v___f_3035_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3035_, 0, v_toSeq_3022_);
                if v_isShared_3027_ == 0 {
                    leanh::lean_ctor_set(v___x_3026_, 4, v___f_3033_);
                    leanh::lean_ctor_set(v___x_3026_, 3, v___f_3034_);
                    leanh::lean_ctor_set(v___x_3026_, 2, v___f_3035_);
                    leanh::lean_ctor_set(v___x_3026_, 1, v___f_3028_);
                    leanh::lean_ctor_set(v___x_3026_, 0, v___x_3032_);
                    v___x_3037_ = v___x_3026_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3075_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3032_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3075_, 1, v___f_3028_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3075_, 2, v___f_3035_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3075_, 3, v___f_3034_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3075_, 4, v___f_3033_);
                    v___x_3037_ = v_reuseFailAlloc_3075_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3020_ == 0 {
                    leanh::lean_ctor_set(v___x_3019_, 1, v___f_3029_);
                    leanh::lean_ctor_set(v___x_3019_, 0, v___x_3037_);
                    v___x_3039_ = v___x_3019_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3074_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3037_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3074_, 1, v___f_3029_);
                    v___x_3039_ = v_reuseFailAlloc_3074_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3040_ = l_StateRefT_x27_instMonad___redArg(v___x_3039_);
                v_toApplicative_3041_ = leanh::lean_ctor_get(v___x_3040_, 0);
                v_isSharedCheck_3072_ = (!leanh::lean_is_exclusive(v___x_3040_)) as u8;
                if v_isSharedCheck_3072_ == 0 {
                    v_unused_3073_ = leanh::lean_ctor_get(v___x_3040_, 1);
                    leanh::lean_dec(v_unused_3073_);
                    v___x_3043_ = v___x_3040_;
                    v_isShared_3044_ = v_isSharedCheck_3072_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_3041_);
                    leanh::lean_dec(v___x_3040_);
                    v___x_3043_ = leanh::lean_box(0);
                    v_isShared_3044_ = v_isSharedCheck_3072_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_3045_ = leanh::lean_ctor_get(v_toApplicative_3041_, 0);
                v_toSeq_3046_ = leanh::lean_ctor_get(v_toApplicative_3041_, 2);
                v_toSeqLeft_3047_ = leanh::lean_ctor_get(v_toApplicative_3041_, 3);
                v_toSeqRight_3048_ = leanh::lean_ctor_get(v_toApplicative_3041_, 4);
                v_isSharedCheck_3070_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_3041_)) as u8;
                if v_isSharedCheck_3070_ == 0 {
                    v_unused_3071_ = leanh::lean_ctor_get(v_toApplicative_3041_, 1);
                    leanh::lean_dec(v_unused_3071_);
                    v___x_3050_ = v_toApplicative_3041_;
                    v_isShared_3051_ = v_isSharedCheck_3070_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_3048_);
                    leanh::lean_inc(v_toSeqLeft_3047_);
                    leanh::lean_inc(v_toSeq_3046_);
                    leanh::lean_inc(v_toFunctor_3045_);
                    leanh::lean_dec(v_toApplicative_3041_);
                    v___x_3050_ = leanh::lean_box(0);
                    v_isShared_3051_ = v_isSharedCheck_3070_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_3052_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3;
                v___f_3053_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4;
                leanh::lean_inc_ref(v_toFunctor_3045_);
                v___f_3054_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3054_, 0, v_toFunctor_3045_);
                v___f_3055_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3055_, 0, v_toFunctor_3045_);
                v___x_3056_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3056_, 0, v___f_3054_);
                leanh::lean_ctor_set(v___x_3056_, 1, v___f_3055_);
                v___f_3057_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3057_, 0, v_toSeqRight_3048_);
                v___f_3058_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3058_, 0, v_toSeqLeft_3047_);
                v___f_3059_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3059_, 0, v_toSeq_3046_);
                if v_isShared_3051_ == 0 {
                    leanh::lean_ctor_set(v___x_3050_, 4, v___f_3057_);
                    leanh::lean_ctor_set(v___x_3050_, 3, v___f_3058_);
                    leanh::lean_ctor_set(v___x_3050_, 2, v___f_3059_);
                    leanh::lean_ctor_set(v___x_3050_, 1, v___f_3052_);
                    leanh::lean_ctor_set(v___x_3050_, 0, v___x_3056_);
                    v___x_3061_ = v___x_3050_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3069_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3056_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3069_, 1, v___f_3052_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3069_, 2, v___f_3059_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3069_, 3, v___f_3058_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3069_, 4, v___f_3057_);
                    v___x_3061_ = v_reuseFailAlloc_3069_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3044_ == 0 {
                    leanh::lean_ctor_set(v___x_3043_, 1, v___f_3053_);
                    leanh::lean_ctor_set(v___x_3043_, 0, v___x_3061_);
                    v___x_3063_ = v___x_3043_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3068_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3061_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3068_, 1, v___f_3053_);
                    v___x_3063_ = v_reuseFailAlloc_3068_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3064_ = leanh::lean_box(0);
                v___x_3065_ = l_instInhabitedOfMonad___redArg(v___x_3063_, v___x_3064_);
                v___x_17258__overap_3066_ = lean_panic_fn_borrowed(v___x_3065_, v_msg_3009_);
                leanh::lean_dec(v___x_3065_);
                leanh::lean_inc(v___y_3013_);
                leanh::lean_inc_ref(v___y_3012_);
                leanh::lean_inc(v___y_3011_);
                leanh::lean_inc_ref(v___y_3010_);
                v___x_3067_ = leanh::lean_apply_5(
                    v___x_17258__overap_3066_,
                    v___y_3010_,
                    v___y_3011_,
                    v___y_3012_,
                    v___y_3013_,
                    leanh::lean_box(0),
                );
                return v___x_3067_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___boxed(
    mut v_msg_3080_: *mut leanh::LeanObject,
    mut v___y_3081_: *mut leanh::LeanObject,
    mut v___y_3082_: *mut leanh::LeanObject,
    mut v___y_3083_: *mut leanh::LeanObject,
    mut v___y_3084_: *mut leanh::LeanObject,
    mut v___y_3085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3086_ =
        l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(
            v_msg_3080_,
            v___y_3081_,
            v___y_3082_,
            v___y_3083_,
            v___y_3084_,
        );
    leanh::lean_dec(v___y_3084_);
    leanh::lean_dec_ref(v___y_3083_);
    leanh::lean_dec(v___y_3082_);
    leanh::lean_dec_ref(v___y_3081_);
    return v_res_3086_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13_spec__19(
    mut v_msgData_3087_: *mut leanh::LeanObject,
    mut v___y_3088_: *mut leanh::LeanObject,
    mut v___y_3089_: *mut leanh::LeanObject,
    mut v___y_3090_: *mut leanh::LeanObject,
    mut v___y_3091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3093_ = lean_st_ref_get(v___y_3091_);
    v_env_3094_ = leanh::lean_ctor_get(v___x_3093_, 0);
    leanh::lean_inc_ref(v_env_3094_);
    leanh::lean_dec(v___x_3093_);
    v___x_3095_ = lean_st_ref_get(v___y_3089_);
    v_mctx_3096_ = leanh::lean_ctor_get(v___x_3095_, 0);
    leanh::lean_inc_ref(v_mctx_3096_);
    leanh::lean_dec(v___x_3095_);
    v_lctx_3097_ = leanh::lean_ctor_get(v___y_3088_, 2);
    v_options_3098_ = leanh::lean_ctor_get(v___y_3090_, 2);
    leanh::lean_inc_ref(v_options_3098_);
    leanh::lean_inc_ref(v_lctx_3097_);
    v___x_3099_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3099_, 0, v_env_3094_);
    leanh::lean_ctor_set(v___x_3099_, 1, v_mctx_3096_);
    leanh::lean_ctor_set(v___x_3099_, 2, v_lctx_3097_);
    leanh::lean_ctor_set(v___x_3099_, 3, v_options_3098_);
    v___x_3100_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3100_, 0, v___x_3099_);
    leanh::lean_ctor_set(v___x_3100_, 1, v_msgData_3087_);
    v___x_3101_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3101_, 0, v___x_3100_);
    return v___x_3101_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13_spec__19___boxed(
    mut v_msgData_3102_: *mut leanh::LeanObject,
    mut v___y_3103_: *mut leanh::LeanObject,
    mut v___y_3104_: *mut leanh::LeanObject,
    mut v___y_3105_: *mut leanh::LeanObject,
    mut v___y_3106_: *mut leanh::LeanObject,
    mut v___y_3107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3108_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13_spec__19(v_msgData_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
    leanh::lean_dec(v___y_3106_);
    leanh::lean_dec_ref(v___y_3105_);
    leanh::lean_dec(v___y_3104_);
    leanh::lean_dec_ref(v___y_3103_);
    return v_res_3108_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(
    mut v_msg_3109_: *mut leanh::LeanObject,
    mut v___y_3110_: *mut leanh::LeanObject,
    mut v___y_3111_: *mut leanh::LeanObject,
    mut v___y_3112_: *mut leanh::LeanObject,
    mut v___y_3113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3120_: u8 = 0;
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3115_ = leanh::lean_ctor_get(v___y_3112_, 5);
                v___x_3116_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13_spec__19(v_msg_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
                v_a_3117_ = leanh::lean_ctor_get(v___x_3116_, 0);
                v_isSharedCheck_3125_ = (!leanh::lean_is_exclusive(v___x_3116_)) as u8;
                if v_isSharedCheck_3125_ == 0 {
                    v___x_3119_ = v___x_3116_;
                    v_isShared_3120_ = v_isSharedCheck_3125_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3117_);
                    leanh::lean_dec(v___x_3116_);
                    v___x_3119_ = leanh::lean_box(0);
                    v_isShared_3120_ = v_isSharedCheck_3125_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3115_);
                v___x_3121_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3121_, 0, v_ref_3115_);
                leanh::lean_ctor_set(v___x_3121_, 1, v_a_3117_);
                if v_isShared_3120_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3119_, 1);
                    leanh::lean_ctor_set(v___x_3119_, 0, v___x_3121_);
                    v___x_3123_ = v___x_3119_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3124_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3121_);
                    v___x_3123_ = v_reuseFailAlloc_3124_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3123_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg___boxed(
    mut v_msg_3126_: *mut leanh::LeanObject,
    mut v___y_3127_: *mut leanh::LeanObject,
    mut v___y_3128_: *mut leanh::LeanObject,
    mut v___y_3129_: *mut leanh::LeanObject,
    mut v___y_3130_: *mut leanh::LeanObject,
    mut v___y_3131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3132_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(
        v_msg_3126_,
        v___y_3127_,
        v___y_3128_,
        v___y_3129_,
        v___y_3130_,
    );
    leanh::lean_dec(v___y_3130_);
    leanh::lean_dec_ref(v___y_3129_);
    leanh::lean_dec(v___y_3128_);
    leanh::lean_dec_ref(v___y_3127_);
    return v_res_3132_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3134_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0;
    v___x_3135_ = l_Lean_stringToMessageData(v___x_3134_);
    return v___x_3135_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3137_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2;
    v___x_3138_ = l_Lean_stringToMessageData(v___x_3137_);
    return v___x_3138_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3142_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6;
    v___x_3143_ = leanh::lean_unsigned_to_nat(11);
    v___x_3144_ = leanh::lean_unsigned_to_nat(122);
    v___x_3145_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5;
    v___x_3146_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4;
    v___x_3147_ = l_mkPanicMessageWithDecl(
        v___x_3146_,
        v___x_3145_,
        v___x_3144_,
        v___x_3143_,
        v___x_3142_,
    );
    return v___x_3147_;
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(
    mut v_constName_3148_: *mut leanh::LeanObject,
    mut v___y_3149_: *mut leanh::LeanObject,
    mut v___y_3150_: *mut leanh::LeanObject,
    mut v___y_3151_: *mut leanh::LeanObject,
    mut v___y_3152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: u8 = 0;
    let mut v___x_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: u8 = 0;
    let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3167_: u8 = 0;
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3172_: u8 = 0;
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3176_: u8 = 0;
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3182_: u8 = 0;
    let mut v_val_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3187_: u8 = 0;
    let mut v_a_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3191_: u8 = 0;
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3195_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3162_ = lean_st_ref_get(v___y_3152_);
                v_env_3163_ = leanh::lean_ctor_get(v___x_3162_, 0);
                leanh::lean_inc_ref(v_env_3163_);
                leanh::lean_dec(v___x_3162_);
                v___x_3164_ = 0;
                leanh::lean_inc(v_constName_3148_);
                v___x_3165_ =
                    l_Lean_Environment_findAsync_x3f(v_env_3163_, v_constName_3148_, v___x_3164_);
                if leanh::lean_obj_tag(v___x_3165_) == 1 {
                    v_val_3166_ = leanh::lean_ctor_get(v___x_3165_, 0);
                    leanh::lean_inc(v_val_3166_);
                    leanh::lean_dec_ref_known(v___x_3165_, 1);
                    v_kind_3167_ = leanh::lean_ctor_get_uint8(
                        v_val_3166_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    if v_kind_3167_ == 6 {
                        v___x_3168_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_3166_);
                        if leanh::lean_obj_tag(v___x_3168_) == 6 {
                            leanh::lean_dec(v_constName_3148_);
                            v_val_3169_ = leanh::lean_ctor_get(v___x_3168_, 0);
                            v_isSharedCheck_3176_ =
                                (!leanh::lean_is_exclusive(v___x_3168_)) as u8;
                            if v_isSharedCheck_3176_ == 0 {
                                v___x_3171_ = v___x_3168_;
                                v_isShared_3172_ = v_isSharedCheck_3176_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_3169_);
                                leanh::lean_dec(v___x_3168_);
                                v___x_3171_ = leanh::lean_box(0);
                                v_isShared_3172_ = v_isSharedCheck_3176_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_3168_);
                            v___x_3177_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__7);
                            v___x_3178_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(v___x_3177_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
                            if leanh::lean_obj_tag(v___x_3178_) == 0 {
                                v_a_3179_ = leanh::lean_ctor_get(v___x_3178_, 0);
                                v_isSharedCheck_3187_ =
                                    (!leanh::lean_is_exclusive(v___x_3178_)) as u8;
                                if v_isSharedCheck_3187_ == 0 {
                                    v___x_3181_ = v___x_3178_;
                                    v_isShared_3182_ = v_isSharedCheck_3187_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3179_);
                                    leanh::lean_dec(v___x_3178_);
                                    v___x_3181_ = leanh::lean_box(0);
                                    v_isShared_3182_ = v_isSharedCheck_3187_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_constName_3148_);
                                v_a_3188_ = leanh::lean_ctor_get(v___x_3178_, 0);
                                v_isSharedCheck_3195_ =
                                    (!leanh::lean_is_exclusive(v___x_3178_)) as u8;
                                if v_isSharedCheck_3195_ == 0 {
                                    v___x_3190_ = v___x_3178_;
                                    v_isShared_3191_ = v_isSharedCheck_3195_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3188_);
                                    leanh::lean_dec(v___x_3178_);
                                    v___x_3190_ = leanh::lean_box(0);
                                    v_isShared_3191_ = v_isSharedCheck_3195_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_3166_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3165_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3155_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
                v___x_3156_ = 0;
                v___x_3157_ = l_Lean_MessageData_ofConstName(v_constName_3148_, v___x_3156_);
                v___x_3158_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3158_, 0, v___x_3155_);
                leanh::lean_ctor_set(v___x_3158_, 1, v___x_3157_);
                v___x_3159_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3);
                v___x_3160_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3160_, 0, v___x_3158_);
                leanh::lean_ctor_set(v___x_3160_, 1, v___x_3159_);
                v___x_3161_ =
                    l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(
                        v___x_3160_,
                        v___y_3149_,
                        v___y_3150_,
                        v___y_3151_,
                        v___y_3152_,
                    );
                return v___x_3161_;
            }
            2 => {
                if v_isShared_3172_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3171_, 0);
                    v___x_3174_ = v___x_3171_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3175_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_val_3169_);
                    v___x_3174_ = v_reuseFailAlloc_3175_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3174_;
            }
            4 => {
                if leanh::lean_obj_tag(v_a_3179_) == 0 {
                    leanh::lean_del_object(v___x_3181_);
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_constName_3148_);
                    v_val_3183_ = leanh::lean_ctor_get(v_a_3179_, 0);
                    leanh::lean_inc(v_val_3183_);
                    leanh::lean_dec_ref_known(v_a_3179_, 1);
                    if v_isShared_3182_ == 0 {
                        leanh::lean_ctor_set(v___x_3181_, 0, v_val_3183_);
                        v___x_3185_ = v___x_3181_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3186_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_val_3183_);
                        v___x_3185_ = v_reuseFailAlloc_3186_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_3185_;
            }
            6 => {
                if v_isShared_3191_ == 0 {
                    v___x_3193_ = v___x_3190_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3194_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3188_);
                    v___x_3193_ = v_reuseFailAlloc_3194_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3193_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___boxed(
    mut v_constName_3196_: *mut leanh::LeanObject,
    mut v___y_3197_: *mut leanh::LeanObject,
    mut v___y_3198_: *mut leanh::LeanObject,
    mut v___y_3199_: *mut leanh::LeanObject,
    mut v___y_3200_: *mut leanh::LeanObject,
    mut v___y_3201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3202_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(
        v_constName_3196_,
        v___y_3197_,
        v___y_3198_,
        v___y_3199_,
        v___y_3200_,
    );
    leanh::lean_dec(v___y_3200_);
    leanh::lean_dec_ref(v___y_3199_);
    leanh::lean_dec(v___y_3198_);
    leanh::lean_dec_ref(v___y_3197_);
    return v_res_3202_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7(
    mut v___x_3203_: *mut leanh::LeanObject,
    mut v_sz_3204_: usize,
    mut v_i_3205_: usize,
    mut v_bs_3206_: *mut leanh::LeanObject,
    mut v___y_3207_: *mut leanh::LeanObject,
    mut v___y_3208_: *mut leanh::LeanObject,
    mut v___y_3209_: *mut leanh::LeanObject,
    mut v___y_3210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3212_: u8 = 0;
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: usize = 0;
    let mut v___x_3225_: usize = 0;
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: u8 = 0;
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3236_: u8 = 0;
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3240_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3212_ = lean_usize_dec_lt(v_i_3205_, v_sz_3204_);
                if v___x_3212_ == 0 {
                    v___x_3213_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3213_, 0, v_bs_3206_);
                    return v___x_3213_;
                } else {
                    v_v_3214_ = lean_array_uget_borrowed(v_bs_3206_, v_i_3205_);
                    leanh::lean_inc(v_v_3214_);
                    v___x_3215_ =
                        l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(
                            v_v_3214_,
                            v___y_3207_,
                            v___y_3208_,
                            v___y_3209_,
                            v___y_3210_,
                        );
                    if leanh::lean_obj_tag(v___x_3215_) == 0 {
                        v_a_3216_ = leanh::lean_ctor_get(v___x_3215_, 0);
                        leanh::lean_inc(v_a_3216_);
                        leanh::lean_dec_ref_known(v___x_3215_, 1);
                        v_cidx_3217_ = leanh::lean_ctor_get(v_a_3216_, 2);
                        leanh::lean_inc(v_cidx_3217_);
                        leanh::lean_dec(v_a_3216_);
                        v_start_3218_ = leanh::lean_ctor_get(v___x_3203_, 1);
                        v_stop_3219_ = leanh::lean_ctor_get(v___x_3203_, 2);
                        v___x_3220_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3221_ = lean_array_uset(v_bs_3206_, v_i_3205_, v___x_3220_);
                        v___x_3228_ = lean_nat_sub(v_stop_3219_, v_start_3218_);
                        v___x_3229_ = lean_nat_dec_lt(v_cidx_3217_, v___x_3228_);
                        leanh::lean_dec(v___x_3228_);
                        if v___x_3229_ == 0 {
                            leanh::lean_dec(v_cidx_3217_);
                            v___x_3230_ = l_Lean_instInhabitedExpr;
                            v___x_3231_ = l_outOfBounds___redArg(v___x_3230_);
                            v_a_3223_ = v___x_3231_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3232_ = l_Subarray_get___redArg(v___x_3203_, v_cidx_3217_);
                            leanh::lean_dec(v_cidx_3217_);
                            v_a_3223_ = v___x_3232_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_bs_3206_);
                        v_a_3233_ = leanh::lean_ctor_get(v___x_3215_, 0);
                        v_isSharedCheck_3240_ =
                            (!leanh::lean_is_exclusive(v___x_3215_)) as u8;
                        if v_isSharedCheck_3240_ == 0 {
                            v___x_3235_ = v___x_3215_;
                            v_isShared_3236_ = v_isSharedCheck_3240_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3233_);
                            leanh::lean_dec(v___x_3215_);
                            v___x_3235_ = leanh::lean_box(0);
                            v_isShared_3236_ = v_isSharedCheck_3240_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3224_ = 1usize;
                v___x_3225_ = lean_usize_add(v_i_3205_, v___x_3224_);
                v___x_3226_ = lean_array_uset(v_bs_x27_3221_, v_i_3205_, v_a_3223_);
                v_i_3205_ = v___x_3225_;
                v_bs_3206_ = v___x_3226_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_3236_ == 0 {
                    v___x_3238_ = v___x_3235_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3239_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3233_);
                    v___x_3238_ = v_reuseFailAlloc_3239_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3238_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7___boxed(
    mut v___x_3241_: *mut leanh::LeanObject,
    mut v_sz_3242_: *mut leanh::LeanObject,
    mut v_i_3243_: *mut leanh::LeanObject,
    mut v_bs_3244_: *mut leanh::LeanObject,
    mut v___y_3245_: *mut leanh::LeanObject,
    mut v___y_3246_: *mut leanh::LeanObject,
    mut v___y_3247_: *mut leanh::LeanObject,
    mut v___y_3248_: *mut leanh::LeanObject,
    mut v___y_3249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3250_: usize = 0;
    let mut v_i_boxed_3251_: usize = 0;
    let mut v_res_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3250_ = leanh::lean_unbox_usize(v_sz_3242_);
    leanh::lean_dec(v_sz_3242_);
    v_i_boxed_3251_ = leanh::lean_unbox_usize(v_i_3243_);
    leanh::lean_dec(v_i_3243_);
    v_res_3252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7(v___x_3241_, v_sz_boxed_3250_, v_i_boxed_3251_, v_bs_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
    leanh::lean_dec(v___y_3248_);
    leanh::lean_dec_ref(v___y_3247_);
    leanh::lean_dec(v___y_3246_);
    leanh::lean_dec_ref(v___y_3245_);
    leanh::lean_dec_ref(v___x_3241_);
    return v_res_3252_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23(
    mut v_xs_3253_: *mut leanh::LeanObject,
    mut v_v_3254_: *mut leanh::LeanObject,
    mut v_i_3255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: u8 = 0;
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: u8 = 0;
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3256_ = lean_array_get_size(v_xs_3253_);
                v___x_3257_ = lean_nat_dec_lt(v_i_3255_, v___x_3256_);
                if v___x_3257_ == 0 {
                    leanh::lean_dec(v_i_3255_);
                    v___x_3258_ = leanh::lean_box(0);
                    return v___x_3258_;
                } else {
                    v___x_3259_ = lean_array_fget_borrowed(v_xs_3253_, v_i_3255_);
                    v___x_3260_ = lean_name_eq(v___x_3259_, v_v_3254_);
                    if v___x_3260_ == 0 {
                        v___x_3261_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3262_ = lean_nat_add(v_i_3255_, v___x_3261_);
                        leanh::lean_dec(v_i_3255_);
                        v_i_3255_ = v___x_3262_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3264_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3264_, 0, v_i_3255_);
                        return v___x_3264_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23___boxed(
    mut v_xs_3265_: *mut leanh::LeanObject,
    mut v_v_3266_: *mut leanh::LeanObject,
    mut v_i_3267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3268_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23(v_xs_3265_, v_v_3266_, v_i_3267_);
    leanh::lean_dec(v_v_3266_);
    leanh::lean_dec_ref(v_xs_3265_);
    return v_res_3268_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15(
    mut v_xs_3269_: *mut leanh::LeanObject,
    mut v_v_3270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3271_ = leanh::lean_unsigned_to_nat(0);
    v___x_3272_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15_spec__23(v_xs_3269_, v_v_3270_, v___x_3271_);
    return v___x_3272_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15___boxed(
    mut v_xs_3273_: *mut leanh::LeanObject,
    mut v_v_3274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3275_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15(v_xs_3273_, v_v_3274_);
    leanh::lean_dec(v_v_3274_);
    leanh::lean_dec_ref(v_xs_3273_);
    return v_res_3275_;
}
pub unsafe fn l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10(
    mut v_xs_3276_: *mut leanh::LeanObject,
    mut v_v_3277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3283_: u8 = 0;
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3278_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__15(v_xs_3276_, v_v_3277_);
                if leanh::lean_obj_tag(v___x_3278_) == 0 {
                    v___x_3279_ = leanh::lean_box(0);
                    return v___x_3279_;
                } else {
                    v_val_3280_ = leanh::lean_ctor_get(v___x_3278_, 0);
                    v_isSharedCheck_3287_ = (!leanh::lean_is_exclusive(v___x_3278_)) as u8;
                    if v_isSharedCheck_3287_ == 0 {
                        v___x_3282_ = v___x_3278_;
                        v_isShared_3283_ = v_isSharedCheck_3287_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3280_);
                        leanh::lean_dec(v___x_3278_);
                        v___x_3282_ = leanh::lean_box(0);
                        v_isShared_3283_ = v_isSharedCheck_3287_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3283_ == 0 {
                    v___x_3285_ = v___x_3282_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3286_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_val_3280_);
                    v___x_3285_ = v_reuseFailAlloc_3286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10___boxed(
    mut v_xs_3288_: *mut leanh::LeanObject,
    mut v_v_3289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3290_ =
        l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10(v_xs_3288_, v_v_3289_);
    leanh::lean_dec(v_v_3289_);
    leanh::lean_dec_ref(v_xs_3288_);
    return v_res_3290_;
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0(
    mut v_ctors_3291_: *mut leanh::LeanObject,
    mut v_a_3292_: *mut leanh::LeanObject,
    mut v___x_3293_: *mut leanh::LeanObject,
    mut v_a_3294_: *mut leanh::LeanObject,
    mut v___x_3295_: u8,
    mut v___x_3296_: u8,
    mut v_a_3297_: *mut leanh::LeanObject,
    mut v_ys_3298_: *mut leanh::LeanObject,
    mut v_x_3299_: *mut leanh::LeanObject,
    mut v___y_3300_: *mut leanh::LeanObject,
    mut v___y_3301_: *mut leanh::LeanObject,
    mut v___y_3302_: *mut leanh::LeanObject,
    mut v___y_3303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: u8 = 0;
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: u8 = 0;
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3328_: u8 = 0;
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3332_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3305_ = l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__10(
                    v_ctors_3291_,
                    v_a_3292_,
                );
                if leanh::lean_obj_tag(v___x_3305_) == 1 {
                    leanh::lean_dec(v_a_3292_);
                    v_val_3306_ = leanh::lean_ctor_get(v___x_3305_, 0);
                    leanh::lean_inc(v_val_3306_);
                    leanh::lean_dec_ref_known(v___x_3305_, 1);
                    leanh::lean_inc_ref(v_ys_3298_);
                    v___x_3307_ = lean_array_pop(v_ys_3298_);
                    v___x_3308_ = lean_array_get_borrowed(v___x_3293_, v_a_3294_, v_val_3306_);
                    leanh::lean_dec(v_val_3306_);
                    leanh::lean_inc(v___x_3308_);
                    v___x_3309_ = l_Lean_mkAppN(v___x_3308_, v___x_3307_);
                    leanh::lean_dec_ref(v___x_3307_);
                    v___x_3310_ = 1;
                    v___x_3311_ = l_Lean_Meta_mkLambdaFVars(
                        v_ys_3298_,
                        v___x_3309_,
                        v___x_3295_,
                        v___x_3296_,
                        v___x_3295_,
                        v___x_3296_,
                        v___x_3310_,
                        v___y_3300_,
                        v___y_3301_,
                        v___y_3302_,
                        v___y_3303_,
                    );
                    leanh::lean_dec_ref(v_ys_3298_);
                    return v___x_3311_;
                } else {
                    leanh::lean_dec(v___x_3305_);
                    v___x_3312_ =
                        l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(
                            v_a_3292_,
                            v___y_3300_,
                            v___y_3301_,
                            v___y_3302_,
                            v___y_3303_,
                        );
                    if leanh::lean_obj_tag(v___x_3312_) == 0 {
                        v_a_3313_ = leanh::lean_ctor_get(v___x_3312_, 0);
                        leanh::lean_inc(v_a_3313_);
                        leanh::lean_dec_ref_known(v___x_3312_, 1);
                        v_cidx_3314_ = leanh::lean_ctor_get(v_a_3313_, 2);
                        leanh::lean_inc(v_cidx_3314_);
                        leanh::lean_dec(v_a_3313_);
                        v___x_3315_ = l_Lean_mkRawNatLit(v_cidx_3314_);
                        v___x_3316_ = l_mkHasNotBitProof(
                            v___x_3315_,
                            v_a_3297_,
                            v___y_3300_,
                            v___y_3301_,
                            v___y_3302_,
                            v___y_3303_,
                        );
                        if leanh::lean_obj_tag(v___x_3316_) == 0 {
                            v_a_3317_ = leanh::lean_ctor_get(v___x_3316_, 0);
                            leanh::lean_inc(v_a_3317_);
                            leanh::lean_dec_ref_known(v___x_3316_, 1);
                            v___x_3318_ = lean_array_get_size(v_ys_3298_);
                            v___x_3319_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3320_ = lean_nat_sub(v___x_3318_, v___x_3319_);
                            v___x_3321_ =
                                lean_array_get_borrowed(v___x_3293_, v_ys_3298_, v___x_3320_);
                            leanh::lean_dec(v___x_3320_);
                            leanh::lean_inc(v___x_3321_);
                            v___x_3322_ = l_Lean_Expr_app___override(v___x_3321_, v_a_3317_);
                            v___x_3323_ = 1;
                            v___x_3324_ = l_Lean_Meta_mkLambdaFVars(
                                v_ys_3298_,
                                v___x_3322_,
                                v___x_3295_,
                                v___x_3296_,
                                v___x_3295_,
                                v___x_3296_,
                                v___x_3323_,
                                v___y_3300_,
                                v___y_3301_,
                                v___y_3302_,
                                v___y_3303_,
                            );
                            leanh::lean_dec_ref(v_ys_3298_);
                            return v___x_3324_;
                        } else {
                            leanh::lean_dec_ref(v_ys_3298_);
                            return v___x_3316_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_ys_3298_);
                        v_a_3325_ = leanh::lean_ctor_get(v___x_3312_, 0);
                        v_isSharedCheck_3332_ =
                            (!leanh::lean_is_exclusive(v___x_3312_)) as u8;
                        if v_isSharedCheck_3332_ == 0 {
                            v___x_3327_ = v___x_3312_;
                            v_isShared_3328_ = v_isSharedCheck_3332_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3325_);
                            leanh::lean_dec(v___x_3312_);
                            v___x_3327_ = leanh::lean_box(0);
                            v_isShared_3328_ = v_isSharedCheck_3332_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3328_ == 0 {
                    v___x_3330_ = v___x_3327_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3331_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
                    v___x_3330_ = v_reuseFailAlloc_3331_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3330_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0___boxed(
    mut v_ctors_3333_: *mut leanh::LeanObject,
    mut v_a_3334_: *mut leanh::LeanObject,
    mut v___x_3335_: *mut leanh::LeanObject,
    mut v_a_3336_: *mut leanh::LeanObject,
    mut v___x_3337_: *mut leanh::LeanObject,
    mut v___x_3338_: *mut leanh::LeanObject,
    mut v_a_3339_: *mut leanh::LeanObject,
    mut v_ys_3340_: *mut leanh::LeanObject,
    mut v_x_3341_: *mut leanh::LeanObject,
    mut v___y_3342_: *mut leanh::LeanObject,
    mut v___y_3343_: *mut leanh::LeanObject,
    mut v___y_3344_: *mut leanh::LeanObject,
    mut v___y_3345_: *mut leanh::LeanObject,
    mut v___y_3346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_21824__boxed_3347_: u8 = 0;
    let mut v___x_21825__boxed_3348_: u8 = 0;
    let mut v_res_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_21824__boxed_3347_ = (leanh::lean_unbox(v___x_3337_) as u8);
    v___x_21825__boxed_3348_ = (leanh::lean_unbox(v___x_3338_) as u8);
    v_res_3349_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0(
        v_ctors_3333_,
        v_a_3334_,
        v___x_3335_,
        v_a_3336_,
        v___x_21824__boxed_3347_,
        v___x_21825__boxed_3348_,
        v_a_3339_,
        v_ys_3340_,
        v_x_3341_,
        v___y_3342_,
        v___y_3343_,
        v___y_3344_,
        v___y_3345_,
    );
    leanh::lean_dec(v___y_3345_);
    leanh::lean_dec_ref(v___y_3344_);
    leanh::lean_dec(v___y_3343_);
    leanh::lean_dec_ref(v___y_3342_);
    leanh::lean_dec_ref(v_x_3341_);
    leanh::lean_dec_ref(v_a_3339_);
    leanh::lean_dec_ref(v_a_3336_);
    leanh::lean_dec_ref(v___x_3335_);
    leanh::lean_dec_ref(v_ctors_3333_);
    return v_res_3349_;
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12(
    mut v_ctors_3350_: *mut leanh::LeanObject,
    mut v_a_3351_: *mut leanh::LeanObject,
    mut v_a_3352_: *mut leanh::LeanObject,
    mut v_as_3353_: *mut leanh::LeanObject,
    mut v_bs_3354_: *mut leanh::LeanObject,
    mut v_i_3355_: *mut leanh::LeanObject,
    mut v_cs_3356_: *mut leanh::LeanObject,
    mut v___y_3357_: *mut leanh::LeanObject,
    mut v___y_3358_: *mut leanh::LeanObject,
    mut v___y_3359_: *mut leanh::LeanObject,
    mut v___y_3360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: u8 = 0;
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: u8 = 0;
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: u8 = 0;
    let mut v_a_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3384_: u8 = 0;
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3388_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3362_ = lean_array_get_size(v_as_3353_);
                v___x_3363_ = lean_nat_dec_lt(v_i_3355_, v___x_3362_);
                if v___x_3363_ == 0 {
                    leanh::lean_dec(v_i_3355_);
                    leanh::lean_dec_ref(v_a_3352_);
                    leanh::lean_dec_ref(v_a_3351_);
                    leanh::lean_dec_ref(v_ctors_3350_);
                    v___x_3364_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3364_, 0, v_cs_3356_);
                    return v___x_3364_;
                } else {
                    v___x_3365_ = lean_array_get_size(v_bs_3354_);
                    v___x_3366_ = lean_nat_dec_lt(v_i_3355_, v___x_3365_);
                    if v___x_3366_ == 0 {
                        leanh::lean_dec(v_i_3355_);
                        leanh::lean_dec_ref(v_a_3352_);
                        leanh::lean_dec_ref(v_a_3351_);
                        leanh::lean_dec_ref(v_ctors_3350_);
                        v___x_3367_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3367_, 0, v_cs_3356_);
                        return v___x_3367_;
                    } else {
                        v___x_3368_ = l_Lean_instInhabitedExpr;
                        v___x_3369_ = 0;
                        v_a_3370_ = lean_array_fget_borrowed(v_as_3353_, v_i_3355_);
                        v___x_3371_ = leanh::lean_box((v___x_3369_) as usize);
                        v___x_3372_ = leanh::lean_box((v___x_3366_) as usize);
                        leanh::lean_inc_ref(v_a_3352_);
                        leanh::lean_inc_ref(v_a_3351_);
                        leanh::lean_inc(v_a_3370_);
                        leanh::lean_inc_ref(v_ctors_3350_);
                        v___f_3373_ = leanh::lean_alloc_closure(l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
                        leanh::lean_closure_set(v___f_3373_, 0, v_ctors_3350_);
                        leanh::lean_closure_set(v___f_3373_, 1, v_a_3370_);
                        leanh::lean_closure_set(v___f_3373_, 2, v___x_3368_);
                        leanh::lean_closure_set(v___f_3373_, 3, v_a_3351_);
                        leanh::lean_closure_set(v___f_3373_, 4, v___x_3371_);
                        leanh::lean_closure_set(v___f_3373_, 5, v___x_3372_);
                        leanh::lean_closure_set(v___f_3373_, 6, v_a_3352_);
                        v_b_3374_ = lean_array_fget_borrowed(v_bs_3354_, v_i_3355_);
                        leanh::lean_inc(v_b_3374_);
                        v___x_3375_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(v_b_3374_, v___f_3373_, v___x_3369_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
                        if leanh::lean_obj_tag(v___x_3375_) == 0 {
                            v_a_3376_ = leanh::lean_ctor_get(v___x_3375_, 0);
                            leanh::lean_inc(v_a_3376_);
                            leanh::lean_dec_ref_known(v___x_3375_, 1);
                            v___x_3377_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3378_ = lean_nat_add(v_i_3355_, v___x_3377_);
                            leanh::lean_dec(v_i_3355_);
                            v___x_3379_ = lean_array_push(v_cs_3356_, v_a_3376_);
                            v_i_3355_ = v___x_3378_;
                            v_cs_3356_ = v___x_3379_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_cs_3356_);
                            leanh::lean_dec(v_i_3355_);
                            leanh::lean_dec_ref(v_a_3352_);
                            leanh::lean_dec_ref(v_a_3351_);
                            leanh::lean_dec_ref(v_ctors_3350_);
                            v_a_3381_ = leanh::lean_ctor_get(v___x_3375_, 0);
                            v_isSharedCheck_3388_ =
                                (!leanh::lean_is_exclusive(v___x_3375_)) as u8;
                            if v_isSharedCheck_3388_ == 0 {
                                v___x_3383_ = v___x_3375_;
                                v_isShared_3384_ = v_isSharedCheck_3388_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3381_);
                                leanh::lean_dec(v___x_3375_);
                                v___x_3383_ = leanh::lean_box(0);
                                v_isShared_3384_ = v_isSharedCheck_3388_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3384_ == 0 {
                    v___x_3386_ = v___x_3383_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3387_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
                    v___x_3386_ = v_reuseFailAlloc_3387_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3386_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12___boxed(
    mut v_ctors_3389_: *mut leanh::LeanObject,
    mut v_a_3390_: *mut leanh::LeanObject,
    mut v_a_3391_: *mut leanh::LeanObject,
    mut v_as_3392_: *mut leanh::LeanObject,
    mut v_bs_3393_: *mut leanh::LeanObject,
    mut v_i_3394_: *mut leanh::LeanObject,
    mut v_cs_3395_: *mut leanh::LeanObject,
    mut v___y_3396_: *mut leanh::LeanObject,
    mut v___y_3397_: *mut leanh::LeanObject,
    mut v___y_3398_: *mut leanh::LeanObject,
    mut v___y_3399_: *mut leanh::LeanObject,
    mut v___y_3400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3401_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12(
        v_ctors_3389_,
        v_a_3390_,
        v_a_3391_,
        v_as_3392_,
        v_bs_3393_,
        v_i_3394_,
        v_cs_3395_,
        v___y_3396_,
        v___y_3397_,
        v___y_3398_,
        v___y_3399_,
    );
    leanh::lean_dec(v___y_3399_);
    leanh::lean_dec_ref(v___y_3398_);
    leanh::lean_dec(v___y_3397_);
    leanh::lean_dec_ref(v___y_3396_);
    leanh::lean_dec_ref(v_bs_3393_);
    leanh::lean_dec_ref(v_as_3392_);
    return v_res_3401_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(
    mut v_sz_3402_: usize,
    mut v_i_3403_: usize,
    mut v_bs_3404_: *mut leanh::LeanObject,
    mut v___y_3405_: *mut leanh::LeanObject,
    mut v___y_3406_: *mut leanh::LeanObject,
    mut v___y_3407_: *mut leanh::LeanObject,
    mut v___y_3408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3410_: u8 = 0;
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: usize = 0;
    let mut v___x_3419_: usize = 0;
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3425_: u8 = 0;
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3429_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3410_ = lean_usize_dec_lt(v_i_3403_, v_sz_3402_);
                if v___x_3410_ == 0 {
                    v___x_3411_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3411_, 0, v_bs_3404_);
                    return v___x_3411_;
                } else {
                    v_v_3412_ = lean_array_uget_borrowed(v_bs_3404_, v_i_3403_);
                    leanh::lean_inc(v_v_3412_);
                    v___x_3413_ =
                        l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(
                            v_v_3412_,
                            v___y_3405_,
                            v___y_3406_,
                            v___y_3407_,
                            v___y_3408_,
                        );
                    if leanh::lean_obj_tag(v___x_3413_) == 0 {
                        v_a_3414_ = leanh::lean_ctor_get(v___x_3413_, 0);
                        leanh::lean_inc(v_a_3414_);
                        leanh::lean_dec_ref_known(v___x_3413_, 1);
                        v_cidx_3415_ = leanh::lean_ctor_get(v_a_3414_, 2);
                        leanh::lean_inc(v_cidx_3415_);
                        leanh::lean_dec(v_a_3414_);
                        v___x_3416_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3417_ = lean_array_uset(v_bs_3404_, v_i_3403_, v___x_3416_);
                        v___x_3418_ = 1usize;
                        v___x_3419_ = lean_usize_add(v_i_3403_, v___x_3418_);
                        v___x_3420_ = lean_array_uset(v_bs_x27_3417_, v_i_3403_, v_cidx_3415_);
                        v_i_3403_ = v___x_3419_;
                        v_bs_3404_ = v___x_3420_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_3404_);
                        v_a_3422_ = leanh::lean_ctor_get(v___x_3413_, 0);
                        v_isSharedCheck_3429_ =
                            (!leanh::lean_is_exclusive(v___x_3413_)) as u8;
                        if v_isSharedCheck_3429_ == 0 {
                            v___x_3424_ = v___x_3413_;
                            v_isShared_3425_ = v_isSharedCheck_3429_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3422_);
                            leanh::lean_dec(v___x_3413_);
                            v___x_3424_ = leanh::lean_box(0);
                            v_isShared_3425_ = v_isSharedCheck_3429_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3425_ == 0 {
                    v___x_3427_ = v___x_3424_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3428_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
                    v___x_3427_ = v_reuseFailAlloc_3428_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3427_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8___boxed(
    mut v_sz_3430_: *mut leanh::LeanObject,
    mut v_i_3431_: *mut leanh::LeanObject,
    mut v_bs_3432_: *mut leanh::LeanObject,
    mut v___y_3433_: *mut leanh::LeanObject,
    mut v___y_3434_: *mut leanh::LeanObject,
    mut v___y_3435_: *mut leanh::LeanObject,
    mut v___y_3436_: *mut leanh::LeanObject,
    mut v___y_3437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3438_: usize = 0;
    let mut v_i_boxed_3439_: usize = 0;
    let mut v_res_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3438_ = leanh::lean_unbox_usize(v_sz_3430_);
    leanh::lean_dec(v_sz_3430_);
    v_i_boxed_3439_ = leanh::lean_unbox_usize(v_i_3431_);
    leanh::lean_dec(v_i_3431_);
    v_res_3440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(v_sz_boxed_3438_, v_i_boxed_3439_, v_bs_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
    leanh::lean_dec(v___y_3436_);
    leanh::lean_dec_ref(v___y_3435_);
    leanh::lean_dec(v___y_3434_);
    leanh::lean_dec_ref(v___y_3433_);
    return v_res_3440_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0(
    mut v_k_3441_: *mut leanh::LeanObject,
    mut v_b_3442_: *mut leanh::LeanObject,
    mut v___y_3443_: *mut leanh::LeanObject,
    mut v___y_3444_: *mut leanh::LeanObject,
    mut v___y_3445_: *mut leanh::LeanObject,
    mut v___y_3446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_3446_);
    leanh::lean_inc_ref(v___y_3445_);
    leanh::lean_inc(v___y_3444_);
    leanh::lean_inc_ref(v___y_3443_);
    v___x_3448_ = leanh::lean_apply_6(
        v_k_3441_,
        v_b_3442_,
        v___y_3443_,
        v___y_3444_,
        v___y_3445_,
        v___y_3446_,
        leanh::lean_box(0),
    );
    return v___x_3448_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0___boxed(
    mut v_k_3449_: *mut leanh::LeanObject,
    mut v_b_3450_: *mut leanh::LeanObject,
    mut v___y_3451_: *mut leanh::LeanObject,
    mut v___y_3452_: *mut leanh::LeanObject,
    mut v___y_3453_: *mut leanh::LeanObject,
    mut v___y_3454_: *mut leanh::LeanObject,
    mut v___y_3455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3456_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0(v_k_3449_, v_b_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
    leanh::lean_dec(v___y_3454_);
    leanh::lean_dec_ref(v___y_3453_);
    leanh::lean_dec(v___y_3452_);
    leanh::lean_dec_ref(v___y_3451_);
    return v_res_3456_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg(
    mut v_name_3457_: *mut leanh::LeanObject,
    mut v_bi_3458_: u8,
    mut v_type_3459_: *mut leanh::LeanObject,
    mut v_k_3460_: *mut leanh::LeanObject,
    mut v_kind_3461_: u8,
    mut v___y_3462_: *mut leanh::LeanObject,
    mut v___y_3463_: *mut leanh::LeanObject,
    mut v___y_3464_: *mut leanh::LeanObject,
    mut v___y_3465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3472_: u8 = 0;
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3476_: u8 = 0;
    let mut v_a_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3480_: u8 = 0;
    let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3484_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3467_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                leanh::lean_closure_set(v___f_3467_, 0, v_k_3460_);
                v___x_3468_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
                    v_name_3457_,
                    v_bi_3458_,
                    v_type_3459_,
                    v___f_3467_,
                    v_kind_3461_,
                    v___y_3462_,
                    v___y_3463_,
                    v___y_3464_,
                    v___y_3465_,
                );
                if leanh::lean_obj_tag(v___x_3468_) == 0 {
                    v_a_3469_ = leanh::lean_ctor_get(v___x_3468_, 0);
                    v_isSharedCheck_3476_ = (!leanh::lean_is_exclusive(v___x_3468_)) as u8;
                    if v_isSharedCheck_3476_ == 0 {
                        v___x_3471_ = v___x_3468_;
                        v_isShared_3472_ = v_isSharedCheck_3476_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3469_);
                        leanh::lean_dec(v___x_3468_);
                        v___x_3471_ = leanh::lean_box(0);
                        v_isShared_3472_ = v_isSharedCheck_3476_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3477_ = leanh::lean_ctor_get(v___x_3468_, 0);
                    v_isSharedCheck_3484_ = (!leanh::lean_is_exclusive(v___x_3468_)) as u8;
                    if v_isSharedCheck_3484_ == 0 {
                        v___x_3479_ = v___x_3468_;
                        v_isShared_3480_ = v_isSharedCheck_3484_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3477_);
                        leanh::lean_dec(v___x_3468_);
                        v___x_3479_ = leanh::lean_box(0);
                        v_isShared_3480_ = v_isSharedCheck_3484_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3472_ == 0 {
                    v___x_3474_ = v___x_3471_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3475_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
                    v___x_3474_ = v_reuseFailAlloc_3475_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3474_;
            }
            3 => {
                if v_isShared_3480_ == 0 {
                    v___x_3482_ = v___x_3479_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3483_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
                    v___x_3482_ = v_reuseFailAlloc_3483_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg___boxed(
    mut v_name_3485_: *mut leanh::LeanObject,
    mut v_bi_3486_: *mut leanh::LeanObject,
    mut v_type_3487_: *mut leanh::LeanObject,
    mut v_k_3488_: *mut leanh::LeanObject,
    mut v_kind_3489_: *mut leanh::LeanObject,
    mut v___y_3490_: *mut leanh::LeanObject,
    mut v___y_3491_: *mut leanh::LeanObject,
    mut v___y_3492_: *mut leanh::LeanObject,
    mut v___y_3493_: *mut leanh::LeanObject,
    mut v___y_3494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_3495_: u8 = 0;
    let mut v_kind_boxed_3496_: u8 = 0;
    let mut v_res_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3495_ = (leanh::lean_unbox(v_bi_3486_) as u8);
    v_kind_boxed_3496_ = (leanh::lean_unbox(v_kind_3489_) as u8);
    v_res_3497_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg(v_name_3485_, v_bi_boxed_3495_, v_type_3487_, v_k_3488_, v_kind_boxed_3496_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
    leanh::lean_dec(v___y_3493_);
    leanh::lean_dec_ref(v___y_3492_);
    leanh::lean_dec(v___y_3491_);
    leanh::lean_dec_ref(v___y_3490_);
    return v_res_3497_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg(
    mut v_name_3498_: *mut leanh::LeanObject,
    mut v_type_3499_: *mut leanh::LeanObject,
    mut v_k_3500_: *mut leanh::LeanObject,
    mut v___y_3501_: *mut leanh::LeanObject,
    mut v___y_3502_: *mut leanh::LeanObject,
    mut v___y_3503_: *mut leanh::LeanObject,
    mut v___y_3504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3506_: u8 = 0;
    let mut v___x_3507_: u8 = 0;
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3506_ = 0;
    v___x_3507_ = 0;
    v___x_3508_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg(v_name_3498_, v___x_3506_, v_type_3499_, v_k_3500_, v___x_3507_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
    return v___x_3508_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg___boxed(
    mut v_name_3509_: *mut leanh::LeanObject,
    mut v_type_3510_: *mut leanh::LeanObject,
    mut v_k_3511_: *mut leanh::LeanObject,
    mut v___y_3512_: *mut leanh::LeanObject,
    mut v___y_3513_: *mut leanh::LeanObject,
    mut v___y_3514_: *mut leanh::LeanObject,
    mut v___y_3515_: *mut leanh::LeanObject,
    mut v___y_3516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3517_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg(
        v_name_3509_,
        v_type_3510_,
        v_k_3511_,
        v___y_3512_,
        v___y_3513_,
        v___y_3514_,
        v___y_3515_,
    );
    leanh::lean_dec(v___y_3515_);
    leanh::lean_dec_ref(v___y_3514_);
    leanh::lean_dec(v___y_3513_);
    leanh::lean_dec_ref(v___y_3512_);
    return v_res_3517_;
}
pub unsafe fn _init_l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3527_ = l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5;
    v___x_3528_ = l_Lean_stringToMessageData(v___x_3527_);
    return v___x_3528_;
}
pub unsafe fn l_Lean_Meta_mkSparseCasesOn___lam__2(
    mut v_numParams_3529_: *mut leanh::LeanObject,
    mut v___x_3530_: *mut leanh::LeanObject,
    mut v_numIndices_3531_: *mut leanh::LeanObject,
    mut v_ctors_3532_: *mut leanh::LeanObject,
    mut v___x_3533_: *mut leanh::LeanObject,
    mut v___x_3534_: *mut leanh::LeanObject,
    mut v_a_3535_: *mut leanh::LeanObject,
    mut v_ctors_3536_: *mut leanh::LeanObject,
    mut v___x_3537_: *mut leanh::LeanObject,
    mut v_xs_3538_: *mut leanh::LeanObject,
    mut v_x_3539_: *mut leanh::LeanObject,
    mut v___y_3540_: *mut leanh::LeanObject,
    mut v___y_3541_: *mut leanh::LeanObject,
    mut v___y_3542_: *mut leanh::LeanObject,
    mut v___y_3543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3561_: usize = 0;
    let mut v___x_3562_: usize = 0;
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: u8 = 0;
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: u8 = 0;
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: u8 = 0;
    let mut v___x_3590_: u8 = 0;
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3616_: u8 = 0;
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3620_: u8 = 0;
    let mut v_a_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3624_: u8 = 0;
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3628_: u8 = 0;
    let mut v_a_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3632_: u8 = 0;
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3636_: u8 = 0;
    let mut v_a_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3640_: u8 = 0;
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3644_: u8 = 0;
    let mut v_a_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3648_: u8 = 0;
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3652_: u8 = 0;
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: u8 = 0;
    let mut v___x_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3670_: u8 = 0;
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3674_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3653_ = lean_array_get_size(v_xs_3538_);
                v___x_3654_ = leanh::lean_unsigned_to_nat(1);
                v___x_3655_ = lean_nat_add(v_numParams_3529_, v___x_3654_);
                v___x_3656_ = lean_nat_add(v___x_3655_, v_numIndices_3531_);
                leanh::lean_dec(v___x_3655_);
                v___x_3657_ = lean_nat_add(v___x_3656_, v___x_3654_);
                leanh::lean_dec(v___x_3656_);
                v___x_3658_ = l_List_lengthTR___redArg(v_ctors_3536_);
                v___x_3659_ = lean_nat_add(v___x_3657_, v___x_3658_);
                leanh::lean_dec(v___x_3658_);
                leanh::lean_dec(v___x_3657_);
                v___x_3660_ = lean_nat_dec_eq(v___x_3653_, v___x_3659_);
                leanh::lean_dec(v___x_3659_);
                if v___x_3660_ == 0 {
                    leanh::lean_dec_ref(v_xs_3538_);
                    leanh::lean_dec(v_ctors_3536_);
                    leanh::lean_dec(v___x_3534_);
                    leanh::lean_dec(v___x_3533_);
                    leanh::lean_dec_ref(v_ctors_3532_);
                    leanh::lean_dec(v_numParams_3529_);
                    v___x_3661_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6_once
                        ),
                        _init_l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6,
                    );
                    v___x_3662_ = l_Lean_MessageData_ofConstName(v___x_3537_, v___x_3660_);
                    v___x_3663_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3663_, 0, v___x_3661_);
                    leanh::lean_ctor_set(v___x_3663_, 1, v___x_3662_);
                    v___x_3664_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
                    v___x_3665_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3665_, 0, v___x_3663_);
                    leanh::lean_ctor_set(v___x_3665_, 1, v___x_3664_);
                    v___x_3666_ =
                        l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(
                            v___x_3665_,
                            v___y_3540_,
                            v___y_3541_,
                            v___y_3542_,
                            v___y_3543_,
                        );
                    v_a_3667_ = leanh::lean_ctor_get(v___x_3666_, 0);
                    v_isSharedCheck_3674_ = (!leanh::lean_is_exclusive(v___x_3666_)) as u8;
                    if v_isSharedCheck_3674_ == 0 {
                        v___x_3669_ = v___x_3666_;
                        v_isShared_3670_ = v_isSharedCheck_3674_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3667_);
                        leanh::lean_dec(v___x_3666_);
                        v___x_3669_ = leanh::lean_box(0);
                        v_isShared_3670_ = v_isSharedCheck_3674_;
                        state = 12;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3537_);
                    v___y_3546_ = v___y_3540_;
                    v___y_3547_ = v___y_3541_;
                    v___y_3548_ = v___y_3542_;
                    v___y_3549_ = v___y_3543_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3550_ = leanh::lean_unsigned_to_nat(0);
                leanh::lean_inc(v_numParams_3529_);
                leanh::lean_inc_ref_n(v_xs_3538_, 2);
                v___x_3551_ =
                    l_Array_toSubarray___redArg(v_xs_3538_, v___x_3550_, v_numParams_3529_);
                v___x_3552_ = lean_array_get(v___x_3530_, v_xs_3538_, v_numParams_3529_);
                v___x_3553_ = leanh::lean_unsigned_to_nat(1);
                v___x_3554_ = lean_nat_add(v_numParams_3529_, v___x_3553_);
                leanh::lean_dec(v_numParams_3529_);
                v___x_3555_ = lean_nat_add(v___x_3554_, v_numIndices_3531_);
                leanh::lean_inc(v___x_3555_);
                v___x_3556_ = l_Array_toSubarray___redArg(v_xs_3538_, v___x_3554_, v___x_3555_);
                v___x_3557_ = lean_array_get(v___x_3530_, v_xs_3538_, v___x_3555_);
                v___x_3558_ = lean_nat_add(v___x_3555_, v___x_3553_);
                leanh::lean_dec(v___x_3555_);
                v___x_3559_ = lean_array_get_size(v_xs_3538_);
                v___x_3560_ = l_Array_toSubarray___redArg(v_xs_3538_, v___x_3558_, v___x_3559_);
                v_sz_3561_ = lean_array_size(v_ctors_3532_);
                v___x_3562_ = 0usize;
                leanh::lean_inc_ref(v_ctors_3532_);
                v___x_3563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__7(v___x_3560_, v_sz_3561_, v___x_3562_, v_ctors_3532_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
                leanh::lean_dec_ref(v___x_3560_);
                if leanh::lean_obj_tag(v___x_3563_) == 0 {
                    v_a_3564_ = leanh::lean_ctor_get(v___x_3563_, 0);
                    leanh::lean_inc(v_a_3564_);
                    leanh::lean_dec_ref_known(v___x_3563_, 1);
                    leanh::lean_inc_ref(v_ctors_3532_);
                    v___x_3565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(v_sz_3561_, v___x_3562_, v_ctors_3532_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
                    if leanh::lean_obj_tag(v___x_3565_) == 0 {
                        v_a_3566_ = leanh::lean_ctor_get(v___x_3565_, 0);
                        leanh::lean_inc(v_a_3566_);
                        leanh::lean_dec_ref_known(v___x_3565_, 1);
                        v___x_3567_ = l_Subarray_copy___redArg(v___x_3556_);
                        v___x_3568_ = lean_mk_empty_array_with_capacity(v___x_3553_);
                        leanh::lean_inc(v___x_3557_);
                        leanh::lean_inc_ref_n(v___x_3568_, 2);
                        v___x_3569_ = lean_array_push(v___x_3568_, v___x_3557_);
                        leanh::lean_inc_ref(v___x_3567_);
                        v___x_3570_ = l_Array_append___redArg(v___x_3567_, v___x_3569_);
                        leanh::lean_inc_ref(v___x_3570_);
                        leanh::lean_inc(v___x_3552_);
                        v___f_3571_ = leanh::lean_alloc_closure(
                            l_Lean_Meta_mkSparseCasesOn___lam__1___boxed as *mut core::ffi::c_void,
                            9,
                            3,
                        );
                        leanh::lean_closure_set(v___f_3571_, 0, v___x_3568_);
                        leanh::lean_closure_set(v___f_3571_, 1, v___x_3552_);
                        leanh::lean_closure_set(v___f_3571_, 2, v___x_3570_);
                        v___x_3572_ = l_Lean_mkConst(v___x_3533_, v___x_3534_);
                        v___x_3573_ = l_Subarray_copy___redArg(v___x_3551_);
                        leanh::lean_inc_ref(v___x_3573_);
                        v___x_3574_ = l_Array_append___redArg(v___x_3573_, v___x_3567_);
                        v___x_3575_ = l_Array_append___redArg(v___x_3574_, v___x_3569_);
                        v___x_3576_ = l_Lean_mkAppN(v___x_3572_, v___x_3575_);
                        leanh::lean_dec_ref(v___x_3575_);
                        v___x_3577_ = l_mkHasNotBit(v___x_3576_, v_a_3566_);
                        v___x_3578_ = l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1;
                        v___x_3579_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg(v___x_3578_, v___x_3577_, v___f_3571_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
                        if leanh::lean_obj_tag(v___x_3579_) == 0 {
                            v_a_3580_ = leanh::lean_ctor_get(v___x_3579_, 0);
                            leanh::lean_inc(v_a_3580_);
                            leanh::lean_dec_ref_known(v___x_3579_, 1);
                            v___x_3581_ = l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3;
                            v___x_3582_ =
                                l_Lean_Core_mkFreshUserName(v___x_3581_, v___y_3548_, v___y_3549_);
                            if leanh::lean_obj_tag(v___x_3582_) == 0 {
                                v_a_3583_ = leanh::lean_ctor_get(v___x_3582_, 0);
                                leanh::lean_inc(v_a_3583_);
                                leanh::lean_dec_ref_known(v___x_3582_, 1);
                                v___x_3584_ = 0;
                                v___x_3585_ = l_Lean_ConstantInfo_value_x21(v_a_3535_, v___x_3584_);
                                v___x_3586_ = 0;
                                leanh::lean_inc(v___x_3552_);
                                v___x_3587_ = l_Lean_mkAppN(v___x_3552_, v___x_3570_);
                                v___x_3588_ =
                                    l_Lean_mkForall(v_a_3583_, v___x_3586_, v_a_3580_, v___x_3587_);
                                v___x_3589_ = 1;
                                v___x_3590_ = 1;
                                v___x_3591_ = l_Lean_Meta_mkLambdaFVars(
                                    v___x_3570_,
                                    v___x_3588_,
                                    v___x_3584_,
                                    v___x_3589_,
                                    v___x_3584_,
                                    v___x_3589_,
                                    v___x_3590_,
                                    v___y_3546_,
                                    v___y_3547_,
                                    v___y_3548_,
                                    v___y_3549_,
                                );
                                leanh::lean_dec_ref(v___x_3570_);
                                if leanh::lean_obj_tag(v___x_3591_) == 0 {
                                    v_a_3592_ = leanh::lean_ctor_get(v___x_3591_, 0);
                                    leanh::lean_inc(v_a_3592_);
                                    leanh::lean_dec_ref_known(v___x_3591_, 1);
                                    v___x_3593_ = l_Lean_mkAppN(v___x_3585_, v___x_3573_);
                                    v___x_3594_ =
                                        l_Lean_Expr_app___override(v___x_3593_, v_a_3592_);
                                    v___x_3595_ = l_Lean_mkAppN(v___x_3594_, v___x_3567_);
                                    v___x_3596_ =
                                        l_Lean_Expr_app___override(v___x_3595_, v___x_3557_);
                                    v___x_3597_ = l_List_lengthTR___redArg(v_ctors_3536_);
                                    leanh::lean_inc_ref(v___x_3596_);
                                    v___x_3598_ = l_Lean_Meta_inferArgumentTypesN(
                                        v___x_3597_,
                                        v___x_3596_,
                                        v___y_3546_,
                                        v___y_3547_,
                                        v___y_3548_,
                                        v___y_3549_,
                                    );
                                    if leanh::lean_obj_tag(v___x_3598_) == 0 {
                                        v_a_3599_ = leanh::lean_ctor_get(v___x_3598_, 0);
                                        leanh::lean_inc(v_a_3599_);
                                        leanh::lean_dec_ref_known(v___x_3598_, 1);
                                        v___x_3600_ = lean_array_mk(v_ctors_3536_);
                                        v___x_3601_ =
                                            l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4;
                                        leanh::lean_inc(v_a_3564_);
                                        v___x_3602_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__12(v_ctors_3532_, v_a_3564_, v_a_3566_, v___x_3600_, v_a_3599_, v___x_3550_, v___x_3601_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
                                        leanh::lean_dec(v_a_3599_);
                                        leanh::lean_dec_ref(v___x_3600_);
                                        if leanh::lean_obj_tag(v___x_3602_) == 0 {
                                            v_a_3603_ = leanh::lean_ctor_get(v___x_3602_, 0);
                                            leanh::lean_inc(v_a_3603_);
                                            leanh::lean_dec_ref_known(v___x_3602_, 1);
                                            v___x_3604_ = l_Lean_mkAppN(v___x_3596_, v_a_3603_);
                                            leanh::lean_dec(v_a_3603_);
                                            v___x_3605_ = l_Lean_Core_betaReduce(
                                                v___x_3604_,
                                                v___y_3548_,
                                                v___y_3549_,
                                            );
                                            if leanh::lean_obj_tag(v___x_3605_) == 0 {
                                                v_a_3606_ =
                                                    leanh::lean_ctor_get(v___x_3605_, 0);
                                                leanh::lean_inc(v_a_3606_);
                                                leanh::lean_dec_ref_known(v___x_3605_, 1);
                                                v___x_3607_ =
                                                    lean_array_push(v___x_3568_, v___x_3552_);
                                                v___x_3608_ = l_Array_append___redArg(
                                                    v___x_3573_,
                                                    v___x_3607_,
                                                );
                                                leanh::lean_dec_ref(v___x_3607_);
                                                v___x_3609_ = l_Array_append___redArg(
                                                    v___x_3608_,
                                                    v___x_3567_,
                                                );
                                                leanh::lean_dec_ref(v___x_3567_);
                                                v___x_3610_ = l_Array_append___redArg(
                                                    v___x_3609_,
                                                    v___x_3569_,
                                                );
                                                leanh::lean_dec_ref(v___x_3569_);
                                                v___x_3611_ =
                                                    l_Array_append___redArg(v___x_3610_, v_a_3564_);
                                                leanh::lean_dec(v_a_3564_);
                                                v___x_3612_ = l_Lean_Meta_mkLambdaFVars(
                                                    v___x_3611_,
                                                    v_a_3606_,
                                                    v___x_3584_,
                                                    v___x_3589_,
                                                    v___x_3584_,
                                                    v___x_3589_,
                                                    v___x_3590_,
                                                    v___y_3546_,
                                                    v___y_3547_,
                                                    v___y_3548_,
                                                    v___y_3549_,
                                                );
                                                leanh::lean_dec_ref(v___x_3611_);
                                                return v___x_3612_;
                                            } else {
                                                leanh::lean_dec_ref(v___x_3573_);
                                                leanh::lean_dec_ref(v___x_3569_);
                                                leanh::lean_dec_ref(v___x_3568_);
                                                leanh::lean_dec_ref(v___x_3567_);
                                                leanh::lean_dec(v_a_3564_);
                                                leanh::lean_dec(v___x_3552_);
                                                return v___x_3605_;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_3596_);
                                            leanh::lean_dec_ref(v___x_3573_);
                                            leanh::lean_dec_ref(v___x_3569_);
                                            leanh::lean_dec_ref(v___x_3568_);
                                            leanh::lean_dec_ref(v___x_3567_);
                                            leanh::lean_dec(v_a_3564_);
                                            leanh::lean_dec(v___x_3552_);
                                            v_a_3613_ = leanh::lean_ctor_get(v___x_3602_, 0);
                                            v_isSharedCheck_3620_ =
                                                (!leanh::lean_is_exclusive(v___x_3602_))
                                                    as u8;
                                            if v_isSharedCheck_3620_ == 0 {
                                                v___x_3615_ = v___x_3602_;
                                                v_isShared_3616_ = v_isSharedCheck_3620_;
                                                state = 2;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_3613_);
                                                leanh::lean_dec(v___x_3602_);
                                                v___x_3615_ = leanh::lean_box(0);
                                                v_isShared_3616_ = v_isSharedCheck_3620_;
                                                state = 2;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v___x_3596_);
                                        leanh::lean_dec_ref(v___x_3573_);
                                        leanh::lean_dec_ref(v___x_3569_);
                                        leanh::lean_dec_ref(v___x_3568_);
                                        leanh::lean_dec_ref(v___x_3567_);
                                        leanh::lean_dec(v_a_3566_);
                                        leanh::lean_dec(v_a_3564_);
                                        leanh::lean_dec(v___x_3552_);
                                        leanh::lean_dec(v_ctors_3536_);
                                        leanh::lean_dec_ref(v_ctors_3532_);
                                        v_a_3621_ = leanh::lean_ctor_get(v___x_3598_, 0);
                                        v_isSharedCheck_3628_ =
                                            (!leanh::lean_is_exclusive(v___x_3598_)) as u8;
                                        if v_isSharedCheck_3628_ == 0 {
                                            v___x_3623_ = v___x_3598_;
                                            v_isShared_3624_ = v_isSharedCheck_3628_;
                                            state = 4;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_3621_);
                                            leanh::lean_dec(v___x_3598_);
                                            v___x_3623_ = leanh::lean_box(0);
                                            v_isShared_3624_ = v_isSharedCheck_3628_;
                                            state = 4;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_3585_);
                                    leanh::lean_dec_ref(v___x_3573_);
                                    leanh::lean_dec_ref(v___x_3569_);
                                    leanh::lean_dec_ref(v___x_3568_);
                                    leanh::lean_dec_ref(v___x_3567_);
                                    leanh::lean_dec(v_a_3566_);
                                    leanh::lean_dec(v_a_3564_);
                                    leanh::lean_dec(v___x_3557_);
                                    leanh::lean_dec(v___x_3552_);
                                    leanh::lean_dec(v_ctors_3536_);
                                    leanh::lean_dec_ref(v_ctors_3532_);
                                    return v___x_3591_;
                                }
                            } else {
                                leanh::lean_dec(v_a_3580_);
                                leanh::lean_dec_ref(v___x_3573_);
                                leanh::lean_dec_ref(v___x_3570_);
                                leanh::lean_dec_ref(v___x_3569_);
                                leanh::lean_dec_ref(v___x_3568_);
                                leanh::lean_dec_ref(v___x_3567_);
                                leanh::lean_dec(v_a_3566_);
                                leanh::lean_dec(v_a_3564_);
                                leanh::lean_dec(v___x_3557_);
                                leanh::lean_dec(v___x_3552_);
                                leanh::lean_dec(v_ctors_3536_);
                                leanh::lean_dec_ref(v_ctors_3532_);
                                v_a_3629_ = leanh::lean_ctor_get(v___x_3582_, 0);
                                v_isSharedCheck_3636_ =
                                    (!leanh::lean_is_exclusive(v___x_3582_)) as u8;
                                if v_isSharedCheck_3636_ == 0 {
                                    v___x_3631_ = v___x_3582_;
                                    v_isShared_3632_ = v_isSharedCheck_3636_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3629_);
                                    leanh::lean_dec(v___x_3582_);
                                    v___x_3631_ = leanh::lean_box(0);
                                    v_isShared_3632_ = v_isSharedCheck_3636_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_3573_);
                            leanh::lean_dec_ref(v___x_3570_);
                            leanh::lean_dec_ref(v___x_3569_);
                            leanh::lean_dec_ref(v___x_3568_);
                            leanh::lean_dec_ref(v___x_3567_);
                            leanh::lean_dec(v_a_3566_);
                            leanh::lean_dec(v_a_3564_);
                            leanh::lean_dec(v___x_3557_);
                            leanh::lean_dec(v___x_3552_);
                            leanh::lean_dec(v_ctors_3536_);
                            leanh::lean_dec_ref(v_ctors_3532_);
                            return v___x_3579_;
                        }
                    } else {
                        leanh::lean_dec(v_a_3564_);
                        leanh::lean_dec(v___x_3557_);
                        leanh::lean_dec_ref(v___x_3556_);
                        leanh::lean_dec(v___x_3552_);
                        leanh::lean_dec_ref(v___x_3551_);
                        leanh::lean_dec(v_ctors_3536_);
                        leanh::lean_dec(v___x_3534_);
                        leanh::lean_dec(v___x_3533_);
                        leanh::lean_dec_ref(v_ctors_3532_);
                        v_a_3637_ = leanh::lean_ctor_get(v___x_3565_, 0);
                        v_isSharedCheck_3644_ =
                            (!leanh::lean_is_exclusive(v___x_3565_)) as u8;
                        if v_isSharedCheck_3644_ == 0 {
                            v___x_3639_ = v___x_3565_;
                            v_isShared_3640_ = v_isSharedCheck_3644_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3637_);
                            leanh::lean_dec(v___x_3565_);
                            v___x_3639_ = leanh::lean_box(0);
                            v_isShared_3640_ = v_isSharedCheck_3644_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_3557_);
                    leanh::lean_dec_ref(v___x_3556_);
                    leanh::lean_dec(v___x_3552_);
                    leanh::lean_dec_ref(v___x_3551_);
                    leanh::lean_dec(v_ctors_3536_);
                    leanh::lean_dec(v___x_3534_);
                    leanh::lean_dec(v___x_3533_);
                    leanh::lean_dec_ref(v_ctors_3532_);
                    v_a_3645_ = leanh::lean_ctor_get(v___x_3563_, 0);
                    v_isSharedCheck_3652_ = (!leanh::lean_is_exclusive(v___x_3563_)) as u8;
                    if v_isSharedCheck_3652_ == 0 {
                        v___x_3647_ = v___x_3563_;
                        v_isShared_3648_ = v_isSharedCheck_3652_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3645_);
                        leanh::lean_dec(v___x_3563_);
                        v___x_3647_ = leanh::lean_box(0);
                        v_isShared_3648_ = v_isSharedCheck_3652_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3616_ == 0 {
                    v___x_3618_ = v___x_3615_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3619_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
                    v___x_3618_ = v_reuseFailAlloc_3619_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3618_;
            }
            4 => {
                if v_isShared_3624_ == 0 {
                    v___x_3626_ = v___x_3623_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3627_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
                    v___x_3626_ = v_reuseFailAlloc_3627_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3626_;
            }
            6 => {
                if v_isShared_3632_ == 0 {
                    v___x_3634_ = v___x_3631_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3635_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3629_);
                    v___x_3634_ = v_reuseFailAlloc_3635_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3634_;
            }
            8 => {
                if v_isShared_3640_ == 0 {
                    v___x_3642_ = v___x_3639_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3643_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_a_3637_);
                    v___x_3642_ = v_reuseFailAlloc_3643_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3642_;
            }
            10 => {
                if v_isShared_3648_ == 0 {
                    v___x_3650_ = v___x_3647_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3651_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
                    v___x_3650_ = v_reuseFailAlloc_3651_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3650_;
            }
            12 => {
                if v_isShared_3670_ == 0 {
                    v___x_3672_ = v___x_3669_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3673_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3667_);
                    v___x_3672_ = v_reuseFailAlloc_3673_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkSparseCasesOn___lam__2___boxed(
    mut v_numParams_3675_: *mut leanh::LeanObject,
    mut v___x_3676_: *mut leanh::LeanObject,
    mut v_numIndices_3677_: *mut leanh::LeanObject,
    mut v_ctors_3678_: *mut leanh::LeanObject,
    mut v___x_3679_: *mut leanh::LeanObject,
    mut v___x_3680_: *mut leanh::LeanObject,
    mut v_a_3681_: *mut leanh::LeanObject,
    mut v_ctors_3682_: *mut leanh::LeanObject,
    mut v___x_3683_: *mut leanh::LeanObject,
    mut v_xs_3684_: *mut leanh::LeanObject,
    mut v_x_3685_: *mut leanh::LeanObject,
    mut v___y_3686_: *mut leanh::LeanObject,
    mut v___y_3687_: *mut leanh::LeanObject,
    mut v___y_3688_: *mut leanh::LeanObject,
    mut v___y_3689_: *mut leanh::LeanObject,
    mut v___y_3690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3691_ = l_Lean_Meta_mkSparseCasesOn___lam__2(
        v_numParams_3675_,
        v___x_3676_,
        v_numIndices_3677_,
        v_ctors_3678_,
        v___x_3679_,
        v___x_3680_,
        v_a_3681_,
        v_ctors_3682_,
        v___x_3683_,
        v_xs_3684_,
        v_x_3685_,
        v___y_3686_,
        v___y_3687_,
        v___y_3688_,
        v___y_3689_,
    );
    leanh::lean_dec(v___y_3689_);
    leanh::lean_dec_ref(v___y_3688_);
    leanh::lean_dec(v___y_3687_);
    leanh::lean_dec_ref(v___y_3686_);
    leanh::lean_dec_ref(v_x_3685_);
    leanh::lean_dec_ref(v_a_3681_);
    leanh::lean_dec(v_numIndices_3677_);
    leanh::lean_dec_ref(v___x_3676_);
    return v_res_3691_;
}
pub unsafe fn l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17(
    mut v_a_3692_: *mut leanh::LeanObject,
    mut v_x_3693_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3694_: u8 = 0;
    let mut v_head_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3693_) == 0 {
                    v___x_3694_ = 0;
                    return v___x_3694_;
                } else {
                    v_head_3695_ = leanh::lean_ctor_get(v_x_3693_, 0);
                    v_tail_3696_ = leanh::lean_ctor_get(v_x_3693_, 1);
                    v___x_3697_ = lean_name_eq(v_a_3692_, v_head_3695_);
                    if v___x_3697_ == 0 {
                        v_x_3693_ = v_tail_3696_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3697_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17___boxed(
    mut v_a_3699_: *mut leanh::LeanObject,
    mut v_x_3700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3701_: u8 = 0;
    let mut v_r_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3701_ = l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17(v_a_3699_, v_x_3700_);
    leanh::lean_dec(v_x_3700_);
    leanh::lean_dec(v_a_3699_);
    v_r_3702_ = leanh::lean_box((v_res_3701_) as usize);
    return v_r_3702_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__0;
    v___x_3705_ = l_Lean_stringToMessageData(v___x_3704_);
    return v___x_3705_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__2;
    v___x_3708_ = l_Lean_stringToMessageData(v___x_3707_);
    return v___x_3708_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18(
    mut v_a_3709_: *mut leanh::LeanObject,
    mut v_indName_3710_: *mut leanh::LeanObject,
    mut v_as_3711_: *mut leanh::LeanObject,
    mut v_sz_3712_: usize,
    mut v_i_3713_: usize,
    mut v_b_3714_: *mut leanh::LeanObject,
    mut v___y_3715_: *mut leanh::LeanObject,
    mut v___y_3716_: *mut leanh::LeanObject,
    mut v___y_3717_: *mut leanh::LeanObject,
    mut v___y_3718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: usize = 0;
    let mut v___x_3723_: usize = 0;
    let mut v___x_3725_: u8 = 0;
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: u8 = 0;
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3725_ = lean_usize_dec_lt(v_i_3713_, v_sz_3712_);
                if v___x_3725_ == 0 {
                    leanh::lean_dec(v_indName_3710_);
                    v___x_3726_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3726_, 0, v_b_3714_);
                    return v___x_3726_;
                } else {
                    v_ctors_3727_ = leanh::lean_ctor_get(v_a_3709_, 4);
                    v___x_3728_ = leanh::lean_box(0);
                    v_a_3729_ = lean_array_uget_borrowed(v_as_3711_, v_i_3713_);
                    v___x_3730_ = l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__17(
                        v_a_3729_,
                        v_ctors_3727_,
                    );
                    if v___x_3730_ == 0 {
                        v___x_3731_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__1);
                        leanh::lean_inc(v_a_3729_);
                        v___x_3732_ = l_Lean_MessageData_ofName(v_a_3729_);
                        v___x_3733_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3733_, 0, v___x_3731_);
                        leanh::lean_ctor_set(v___x_3733_, 1, v___x_3732_);
                        v___x_3734_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___closed__3);
                        v___x_3735_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3735_, 0, v___x_3733_);
                        leanh::lean_ctor_set(v___x_3735_, 1, v___x_3734_);
                        leanh::lean_inc(v_indName_3710_);
                        v___x_3736_ = l_Lean_MessageData_ofName(v_indName_3710_);
                        v___x_3737_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3737_, 0, v___x_3735_);
                        leanh::lean_ctor_set(v___x_3737_, 1, v___x_3736_);
                        v___x_3738_ =
                            l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(
                                v___x_3737_,
                                v___y_3715_,
                                v___y_3716_,
                                v___y_3717_,
                                v___y_3718_,
                            );
                        if leanh::lean_obj_tag(v___x_3738_) == 0 {
                            leanh::lean_dec_ref_known(v___x_3738_, 1);
                            v_a_3721_ = v___x_3728_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_indName_3710_);
                            return v___x_3738_;
                        }
                    } else {
                        v_a_3721_ = v___x_3728_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3722_ = 1usize;
                v___x_3723_ = lean_usize_add(v_i_3713_, v___x_3722_);
                v_i_3713_ = v___x_3723_;
                v_b_3714_ = v_a_3721_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18___boxed(
    mut v_a_3739_: *mut leanh::LeanObject,
    mut v_indName_3740_: *mut leanh::LeanObject,
    mut v_as_3741_: *mut leanh::LeanObject,
    mut v_sz_3742_: *mut leanh::LeanObject,
    mut v_i_3743_: *mut leanh::LeanObject,
    mut v_b_3744_: *mut leanh::LeanObject,
    mut v___y_3745_: *mut leanh::LeanObject,
    mut v___y_3746_: *mut leanh::LeanObject,
    mut v___y_3747_: *mut leanh::LeanObject,
    mut v___y_3748_: *mut leanh::LeanObject,
    mut v___y_3749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3750_: usize = 0;
    let mut v_i_boxed_3751_: usize = 0;
    let mut v_res_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3750_ = leanh::lean_unbox_usize(v_sz_3742_);
    leanh::lean_dec(v_sz_3742_);
    v_i_boxed_3751_ = leanh::lean_unbox_usize(v_i_3743_);
    leanh::lean_dec(v_i_3743_);
    v_res_3752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18(v_a_3739_, v_indName_3740_, v_as_3741_, v_sz_boxed_3750_, v_i_boxed_3751_, v_b_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
    leanh::lean_dec(v___y_3748_);
    leanh::lean_dec_ref(v___y_3747_);
    leanh::lean_dec(v___y_3746_);
    leanh::lean_dec_ref(v___y_3745_);
    leanh::lean_dec_ref(v_as_3741_);
    leanh::lean_dec_ref(v_a_3739_);
    return v_res_3752_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__6(
    mut v_a_3753_: *mut leanh::LeanObject,
    mut v_a_3754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3760_: u8 = 0;
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3766_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3753_) == 0 {
                    v___x_3755_ = l_List_reverse___redArg(v_a_3754_);
                    return v___x_3755_;
                } else {
                    v_head_3756_ = leanh::lean_ctor_get(v_a_3753_, 0);
                    v_tail_3757_ = leanh::lean_ctor_get(v_a_3753_, 1);
                    v_isSharedCheck_3766_ = (!leanh::lean_is_exclusive(v_a_3753_)) as u8;
                    if v_isSharedCheck_3766_ == 0 {
                        v___x_3759_ = v_a_3753_;
                        v_isShared_3760_ = v_isSharedCheck_3766_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3757_);
                        leanh::lean_inc(v_head_3756_);
                        leanh::lean_dec(v_a_3753_);
                        v___x_3759_ = leanh::lean_box(0);
                        v_isShared_3760_ = v_isSharedCheck_3766_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3761_ = l_Lean_mkLevelParam(v_head_3756_);
                if v_isShared_3760_ == 0 {
                    leanh::lean_ctor_set(v___x_3759_, 1, v_a_3754_);
                    leanh::lean_ctor_set(v___x_3759_, 0, v___x_3761_);
                    v___x_3763_ = v___x_3759_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3765_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3761_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3765_, 1, v_a_3754_);
                    v___x_3763_ = v_reuseFailAlloc_3765_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3753_ = v_tail_3757_;
                v_a_3754_ = v___x_3763_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3767_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3767_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3768_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__0);
    v___x_3769_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3769_, 0, v___x_3768_);
    return v___x_3769_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3770_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1);
    v___x_3771_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3771_, 0, v___x_3770_);
    leanh::lean_ctor_set(v___x_3771_, 1, v___x_3770_);
    return v___x_3771_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3772_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__1);
    v___x_3773_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_3773_, 0, v___x_3772_);
    leanh::lean_ctor_set(v___x_3773_, 1, v___x_3772_);
    leanh::lean_ctor_set(v___x_3773_, 2, v___x_3772_);
    leanh::lean_ctor_set(v___x_3773_, 3, v___x_3772_);
    leanh::lean_ctor_set(v___x_3773_, 4, v___x_3772_);
    leanh::lean_ctor_set(v___x_3773_, 5, v___x_3772_);
    return v___x_3773_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg(
    mut v_declName_3774_: *mut leanh::LeanObject,
    mut v_s_3775_: u8,
    mut v___y_3776_: *mut leanh::LeanObject,
    mut v___y_3777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3790_: u8 = 0;
    let mut v___x_3791_: u8 = 0;
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3805_: u8 = 0;
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3813_: u8 = 0;
    let mut v_unused_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3816_: u8 = 0;
    let mut v_unused_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3779_ = lean_st_ref_take(v___y_3777_);
                v_env_3780_ = leanh::lean_ctor_get(v___x_3779_, 0);
                v_nextMacroScope_3781_ = leanh::lean_ctor_get(v___x_3779_, 1);
                v_ngen_3782_ = leanh::lean_ctor_get(v___x_3779_, 2);
                v_auxDeclNGen_3783_ = leanh::lean_ctor_get(v___x_3779_, 3);
                v_traceState_3784_ = leanh::lean_ctor_get(v___x_3779_, 4);
                v_messages_3785_ = leanh::lean_ctor_get(v___x_3779_, 6);
                v_infoState_3786_ = leanh::lean_ctor_get(v___x_3779_, 7);
                v_snapshotTasks_3787_ = leanh::lean_ctor_get(v___x_3779_, 8);
                v_isSharedCheck_3816_ = (!leanh::lean_is_exclusive(v___x_3779_)) as u8;
                if v_isSharedCheck_3816_ == 0 {
                    v_unused_3817_ = leanh::lean_ctor_get(v___x_3779_, 5);
                    leanh::lean_dec(v_unused_3817_);
                    v___x_3789_ = v___x_3779_;
                    v_isShared_3790_ = v_isSharedCheck_3816_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3787_);
                    leanh::lean_inc(v_infoState_3786_);
                    leanh::lean_inc(v_messages_3785_);
                    leanh::lean_inc(v_traceState_3784_);
                    leanh::lean_inc(v_auxDeclNGen_3783_);
                    leanh::lean_inc(v_ngen_3782_);
                    leanh::lean_inc(v_nextMacroScope_3781_);
                    leanh::lean_inc(v_env_3780_);
                    leanh::lean_dec(v___x_3779_);
                    v___x_3789_ = leanh::lean_box(0);
                    v_isShared_3790_ = v_isSharedCheck_3816_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3791_ = 0;
                v___x_3792_ = leanh::lean_box(0);
                v___x_3793_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(
                    v_env_3780_,
                    v_declName_3774_,
                    v_s_3775_,
                    v___x_3791_,
                    v___x_3792_,
                );
                v___x_3794_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2);
                if v_isShared_3790_ == 0 {
                    leanh::lean_ctor_set(v___x_3789_, 5, v___x_3794_);
                    leanh::lean_ctor_set(v___x_3789_, 0, v___x_3793_);
                    v___x_3796_ = v___x_3789_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3815_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3793_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 1, v_nextMacroScope_3781_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 2, v_ngen_3782_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 3, v_auxDeclNGen_3783_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 4, v_traceState_3784_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 5, v___x_3794_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 6, v_messages_3785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 7, v_infoState_3786_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 8, v_snapshotTasks_3787_);
                    v___x_3796_ = v_reuseFailAlloc_3815_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3797_ = lean_st_ref_set(v___y_3777_, v___x_3796_);
                v___x_3798_ = lean_st_ref_take(v___y_3776_);
                v_mctx_3799_ = leanh::lean_ctor_get(v___x_3798_, 0);
                v_zetaDeltaFVarIds_3800_ = leanh::lean_ctor_get(v___x_3798_, 2);
                v_postponed_3801_ = leanh::lean_ctor_get(v___x_3798_, 3);
                v_diag_3802_ = leanh::lean_ctor_get(v___x_3798_, 4);
                v_isSharedCheck_3813_ = (!leanh::lean_is_exclusive(v___x_3798_)) as u8;
                if v_isSharedCheck_3813_ == 0 {
                    v_unused_3814_ = leanh::lean_ctor_get(v___x_3798_, 1);
                    leanh::lean_dec(v_unused_3814_);
                    v___x_3804_ = v___x_3798_;
                    v_isShared_3805_ = v_isSharedCheck_3813_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3802_);
                    leanh::lean_inc(v_postponed_3801_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3800_);
                    leanh::lean_inc(v_mctx_3799_);
                    leanh::lean_dec(v___x_3798_);
                    v___x_3804_ = leanh::lean_box(0);
                    v_isShared_3805_ = v_isSharedCheck_3813_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3806_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3);
                if v_isShared_3805_ == 0 {
                    leanh::lean_ctor_set(v___x_3804_, 1, v___x_3806_);
                    v___x_3808_ = v___x_3804_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3812_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_mctx_3799_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3812_, 1, v___x_3806_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3812_,
                        2,
                        v_zetaDeltaFVarIds_3800_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3812_, 3, v_postponed_3801_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3812_, 4, v_diag_3802_);
                    v___x_3808_ = v_reuseFailAlloc_3812_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3809_ = lean_st_ref_set(v___y_3776_, v___x_3808_);
                v___x_3810_ = leanh::lean_box(0);
                v___x_3811_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3811_, 0, v___x_3810_);
                return v___x_3811_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___boxed(
    mut v_declName_3818_: *mut leanh::LeanObject,
    mut v_s_3819_: *mut leanh::LeanObject,
    mut v___y_3820_: *mut leanh::LeanObject,
    mut v___y_3821_: *mut leanh::LeanObject,
    mut v___y_3822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_boxed_3823_: u8 = 0;
    let mut v_res_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_3823_ = (leanh::lean_unbox(v_s_3819_) as u8);
    v_res_3824_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg(v_declName_3818_, v_s_boxed_3823_, v___y_3820_, v___y_3821_);
    leanh::lean_dec(v___y_3821_);
    leanh::lean_dec(v___y_3820_);
    return v_res_3824_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15(
    mut v_declName_3825_: *mut leanh::LeanObject,
    mut v___y_3826_: *mut leanh::LeanObject,
    mut v___y_3827_: *mut leanh::LeanObject,
    mut v___y_3828_: *mut leanh::LeanObject,
    mut v___y_3829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3831_: u8 = 0;
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3831_ = 0;
    v___x_3832_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg(v_declName_3825_, v___x_3831_, v___y_3827_, v___y_3829_);
    return v___x_3832_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15___boxed(
    mut v_declName_3833_: *mut leanh::LeanObject,
    mut v___y_3834_: *mut leanh::LeanObject,
    mut v___y_3835_: *mut leanh::LeanObject,
    mut v___y_3836_: *mut leanh::LeanObject,
    mut v___y_3837_: *mut leanh::LeanObject,
    mut v___y_3838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3839_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15(
        v_declName_3833_,
        v___y_3834_,
        v___y_3835_,
        v___y_3836_,
        v___y_3837_,
    );
    leanh::lean_dec(v___y_3837_);
    leanh::lean_dec_ref(v___y_3836_);
    leanh::lean_dec(v___y_3835_);
    leanh::lean_dec_ref(v___y_3834_);
    return v_res_3839_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3841_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__0;
    v___x_3842_ = l_Lean_stringToMessageData(v___x_3841_);
    return v___x_3842_;
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4(
    mut v_constName_3843_: *mut leanh::LeanObject,
    mut v___y_3844_: *mut leanh::LeanObject,
    mut v___y_3845_: *mut leanh::LeanObject,
    mut v___y_3846_: *mut leanh::LeanObject,
    mut v___y_3847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: u8 = 0;
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3862_: u8 = 0;
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3866_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3849_ = lean_st_ref_get(v___y_3847_);
                v_env_3850_ = leanh::lean_ctor_get(v___x_3849_, 0);
                leanh::lean_inc_ref(v_env_3850_);
                leanh::lean_dec(v___x_3849_);
                leanh::lean_inc(v_constName_3843_);
                v___x_3851_ = l_Lean_isInductiveCore_x3f(v_env_3850_, v_constName_3843_);
                if leanh::lean_obj_tag(v___x_3851_) == 0 {
                    v___x_3852_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
                    v___x_3853_ = 0;
                    v___x_3854_ = l_Lean_MessageData_ofConstName(v_constName_3843_, v___x_3853_);
                    v___x_3855_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3855_, 0, v___x_3852_);
                    leanh::lean_ctor_set(v___x_3855_, 1, v___x_3854_);
                    v___x_3856_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___closed__1);
                    v___x_3857_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3857_, 0, v___x_3855_);
                    leanh::lean_ctor_set(v___x_3857_, 1, v___x_3856_);
                    v___x_3858_ =
                        l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(
                            v___x_3857_,
                            v___y_3844_,
                            v___y_3845_,
                            v___y_3846_,
                            v___y_3847_,
                        );
                    return v___x_3858_;
                } else {
                    leanh::lean_dec(v_constName_3843_);
                    v_val_3859_ = leanh::lean_ctor_get(v___x_3851_, 0);
                    v_isSharedCheck_3866_ = (!leanh::lean_is_exclusive(v___x_3851_)) as u8;
                    if v_isSharedCheck_3866_ == 0 {
                        v___x_3861_ = v___x_3851_;
                        v_isShared_3862_ = v_isSharedCheck_3866_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3859_);
                        leanh::lean_dec(v___x_3851_);
                        v___x_3861_ = leanh::lean_box(0);
                        v_isShared_3862_ = v_isSharedCheck_3866_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3862_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3861_, 0);
                    v___x_3864_ = v___x_3861_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3865_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_val_3859_);
                    v___x_3864_ = v_reuseFailAlloc_3865_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3864_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4___boxed(
    mut v_constName_3867_: *mut leanh::LeanObject,
    mut v___y_3868_: *mut leanh::LeanObject,
    mut v___y_3869_: *mut leanh::LeanObject,
    mut v___y_3870_: *mut leanh::LeanObject,
    mut v___y_3871_: *mut leanh::LeanObject,
    mut v___y_3872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3873_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4(
        v_constName_3867_,
        v___y_3868_,
        v___y_3869_,
        v___y_3870_,
        v___y_3871_,
    );
    leanh::lean_dec(v___y_3871_);
    leanh::lean_dec_ref(v___y_3870_);
    leanh::lean_dec(v___y_3869_);
    leanh::lean_dec_ref(v___y_3868_);
    return v_res_3873_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(
    mut v_ref_3874_: *mut leanh::LeanObject,
    mut v_msg_3875_: *mut leanh::LeanObject,
    mut v___y_3876_: *mut leanh::LeanObject,
    mut v___y_3877_: *mut leanh::LeanObject,
    mut v___y_3878_: *mut leanh::LeanObject,
    mut v___y_3879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3893_: u8 = 0;
    let mut v_cancelTk_x3f_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3895_: u8 = 0;
    let mut v_inheritedTraceOptions_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3881_ = leanh::lean_ctor_get(v___y_3878_, 0);
    v_fileMap_3882_ = leanh::lean_ctor_get(v___y_3878_, 1);
    v_options_3883_ = leanh::lean_ctor_get(v___y_3878_, 2);
    v_currRecDepth_3884_ = leanh::lean_ctor_get(v___y_3878_, 3);
    v_maxRecDepth_3885_ = leanh::lean_ctor_get(v___y_3878_, 4);
    v_ref_3886_ = leanh::lean_ctor_get(v___y_3878_, 5);
    v_currNamespace_3887_ = leanh::lean_ctor_get(v___y_3878_, 6);
    v_openDecls_3888_ = leanh::lean_ctor_get(v___y_3878_, 7);
    v_initHeartbeats_3889_ = leanh::lean_ctor_get(v___y_3878_, 8);
    v_maxHeartbeats_3890_ = leanh::lean_ctor_get(v___y_3878_, 9);
    v_quotContext_3891_ = leanh::lean_ctor_get(v___y_3878_, 10);
    v_currMacroScope_3892_ = leanh::lean_ctor_get(v___y_3878_, 11);
    v_diag_3893_ = leanh::lean_ctor_get_uint8(
        v___y_3878_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3894_ = leanh::lean_ctor_get(v___y_3878_, 12);
    v_suppressElabErrors_3895_ = leanh::lean_ctor_get_uint8(
        v___y_3878_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3896_ = leanh::lean_ctor_get(v___y_3878_, 13);
    v_ref_3897_ = l_Lean_replaceRef(v_ref_3874_, v_ref_3886_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_3896_);
    leanh::lean_inc(v_cancelTk_x3f_3894_);
    leanh::lean_inc(v_currMacroScope_3892_);
    leanh::lean_inc(v_quotContext_3891_);
    leanh::lean_inc(v_maxHeartbeats_3890_);
    leanh::lean_inc(v_initHeartbeats_3889_);
    leanh::lean_inc(v_openDecls_3888_);
    leanh::lean_inc(v_currNamespace_3887_);
    leanh::lean_inc(v_maxRecDepth_3885_);
    leanh::lean_inc(v_currRecDepth_3884_);
    leanh::lean_inc_ref(v_options_3883_);
    leanh::lean_inc_ref(v_fileMap_3882_);
    leanh::lean_inc_ref(v_fileName_3881_);
    v___x_3898_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_3898_, 0, v_fileName_3881_);
    leanh::lean_ctor_set(v___x_3898_, 1, v_fileMap_3882_);
    leanh::lean_ctor_set(v___x_3898_, 2, v_options_3883_);
    leanh::lean_ctor_set(v___x_3898_, 3, v_currRecDepth_3884_);
    leanh::lean_ctor_set(v___x_3898_, 4, v_maxRecDepth_3885_);
    leanh::lean_ctor_set(v___x_3898_, 5, v_ref_3897_);
    leanh::lean_ctor_set(v___x_3898_, 6, v_currNamespace_3887_);
    leanh::lean_ctor_set(v___x_3898_, 7, v_openDecls_3888_);
    leanh::lean_ctor_set(v___x_3898_, 8, v_initHeartbeats_3889_);
    leanh::lean_ctor_set(v___x_3898_, 9, v_maxHeartbeats_3890_);
    leanh::lean_ctor_set(v___x_3898_, 10, v_quotContext_3891_);
    leanh::lean_ctor_set(v___x_3898_, 11, v_currMacroScope_3892_);
    leanh::lean_ctor_set(v___x_3898_, 12, v_cancelTk_x3f_3894_);
    leanh::lean_ctor_set(v___x_3898_, 13, v_inheritedTraceOptions_3896_);
    leanh::lean_ctor_set_uint8(
        v___x_3898_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_3893_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3898_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3895_,
    );
    v___x_3899_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(
        v_msg_3875_,
        v___y_3876_,
        v___y_3877_,
        v___x_3898_,
        v___y_3879_,
    );
    leanh::lean_dec_ref_known(v___x_3898_, 14);
    return v___x_3899_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg___boxed(
    mut v_ref_3900_: *mut leanh::LeanObject,
    mut v_msg_3901_: *mut leanh::LeanObject,
    mut v___y_3902_: *mut leanh::LeanObject,
    mut v___y_3903_: *mut leanh::LeanObject,
    mut v___y_3904_: *mut leanh::LeanObject,
    mut v___y_3905_: *mut leanh::LeanObject,
    mut v___y_3906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3907_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(v_ref_3900_, v_msg_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
    leanh::lean_dec(v___y_3905_);
    leanh::lean_dec_ref(v___y_3904_);
    leanh::lean_dec(v___y_3903_);
    leanh::lean_dec_ref(v___y_3902_);
    leanh::lean_dec(v_ref_3900_);
    return v_res_3907_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3908_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3908_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3909_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__0);
    v___x_3910_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3910_, 0, v___x_3909_);
    return v___x_3910_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3911_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1);
    v___x_3912_ = leanh::lean_unsigned_to_nat(0);
    v___x_3913_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_3913_, 0, v___x_3912_);
    leanh::lean_ctor_set(v___x_3913_, 1, v___x_3912_);
    leanh::lean_ctor_set(v___x_3913_, 2, v___x_3912_);
    leanh::lean_ctor_set(v___x_3913_, 3, v___x_3912_);
    leanh::lean_ctor_set(v___x_3913_, 4, v___x_3911_);
    leanh::lean_ctor_set(v___x_3913_, 5, v___x_3911_);
    leanh::lean_ctor_set(v___x_3913_, 6, v___x_3911_);
    leanh::lean_ctor_set(v___x_3913_, 7, v___x_3911_);
    leanh::lean_ctor_set(v___x_3913_, 8, v___x_3911_);
    leanh::lean_ctor_set(v___x_3913_, 9, v___x_3911_);
    return v___x_3913_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3914_ = leanh::lean_unsigned_to_nat(32);
    v___x_3915_ = lean_mk_empty_array_with_capacity(v___x_3914_);
    v___x_3916_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3916_, 0, v___x_3915_);
    return v___x_3916_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3917_: usize = 0;
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3917_ = 5usize;
    v___x_3918_ = leanh::lean_unsigned_to_nat(0);
    v___x_3919_ = leanh::lean_unsigned_to_nat(32);
    v___x_3920_ = lean_mk_empty_array_with_capacity(v___x_3919_);
    v___x_3921_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__3);
    v___x_3922_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3922_, 0, v___x_3921_);
    leanh::lean_ctor_set(v___x_3922_, 1, v___x_3920_);
    leanh::lean_ctor_set(v___x_3922_, 2, v___x_3918_);
    leanh::lean_ctor_set(v___x_3922_, 3, v___x_3918_);
    leanh::lean_ctor_set_usize(v___x_3922_, 4, v___x_3917_);
    return v___x_3922_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3923_ = leanh::lean_box(1);
    v___x_3924_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__4);
    v___x_3925_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__1);
    v___x_3926_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3926_, 0, v___x_3925_);
    leanh::lean_ctor_set(v___x_3926_, 1, v___x_3924_);
    leanh::lean_ctor_set(v___x_3926_, 2, v___x_3923_);
    return v___x_3926_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3928_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__6;
    v___x_3929_ = l_Lean_stringToMessageData(v___x_3928_);
    return v___x_3929_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3931_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__8;
    v___x_3932_ = l_Lean_stringToMessageData(v___x_3931_);
    return v___x_3932_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3934_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__10;
    v___x_3935_ = l_Lean_stringToMessageData(v___x_3934_);
    return v___x_3935_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3937_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__12;
    v___x_3938_ = l_Lean_stringToMessageData(v___x_3937_);
    return v___x_3938_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3940_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__14;
    v___x_3941_ = l_Lean_stringToMessageData(v___x_3940_);
    return v___x_3941_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3943_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__16;
    v___x_3944_ = l_Lean_stringToMessageData(v___x_3943_);
    return v___x_3944_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3946_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__18;
    v___x_3947_ = l_Lean_stringToMessageData(v___x_3946_);
    return v___x_3947_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(
    mut v_msg_3948_: *mut leanh::LeanObject,
    mut v_declHint_3949_: *mut leanh::LeanObject,
    mut v___y_3950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: u8 = 0;
    let mut v_isExporting_3955_: u8 = 0;
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: u8 = 0;
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3977_: u8 = 0;
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: u8 = 0;
    let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4009_: u8 = 0;
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3952_ = lean_st_ref_get(v___y_3950_);
                v_env_3953_ = leanh::lean_ctor_get(v___x_3952_, 0);
                leanh::lean_inc_ref(v_env_3953_);
                leanh::lean_dec(v___x_3952_);
                v___x_3954_ = l_Lean_Name_isAnonymous(v_declHint_3949_);
                if v___x_3954_ == 0 {
                    v_isExporting_3955_ = leanh::lean_ctor_get_uint8(
                        v_env_3953_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3955_ == 0 {
                        leanh::lean_dec_ref(v_env_3953_);
                        leanh::lean_dec(v_declHint_3949_);
                        v___x_3956_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3956_, 0, v_msg_3948_);
                        return v___x_3956_;
                    } else {
                        leanh::lean_inc_ref(v_env_3953_);
                        v___x_3957_ = l_Lean_Environment_setExporting(v_env_3953_, v___x_3954_);
                        leanh::lean_inc(v_declHint_3949_);
                        leanh::lean_inc_ref(v___x_3957_);
                        v___x_3958_ = l_Lean_Environment_contains(
                            v___x_3957_,
                            v_declHint_3949_,
                            v_isExporting_3955_,
                        );
                        if v___x_3958_ == 0 {
                            leanh::lean_dec_ref(v___x_3957_);
                            leanh::lean_dec_ref(v_env_3953_);
                            leanh::lean_dec(v_declHint_3949_);
                            v___x_3959_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3959_, 0, v_msg_3948_);
                            return v___x_3959_;
                        } else {
                            v___x_3960_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__2);
                            v___x_3961_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__5);
                            v___x_3962_ = l_Lean_Options_empty;
                            v___x_3963_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_3963_, 0, v___x_3957_);
                            leanh::lean_ctor_set(v___x_3963_, 1, v___x_3960_);
                            leanh::lean_ctor_set(v___x_3963_, 2, v___x_3961_);
                            leanh::lean_ctor_set(v___x_3963_, 3, v___x_3962_);
                            leanh::lean_inc(v_declHint_3949_);
                            v___x_3964_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3949_, v___x_3954_);
                            v_c_3965_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_3965_, 0, v___x_3963_);
                            leanh::lean_ctor_set(v_c_3965_, 1, v___x_3964_);
                            v___x_3966_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3953_,
                                v_declHint_3949_,
                            );
                            if leanh::lean_obj_tag(v___x_3966_) == 0 {
                                leanh::lean_dec_ref(v_env_3953_);
                                leanh::lean_dec(v_declHint_3949_);
                                v___x_3967_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7);
                                v___x_3968_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3968_, 0, v___x_3967_);
                                leanh::lean_ctor_set(v___x_3968_, 1, v_c_3965_);
                                v___x_3969_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__9);
                                v___x_3970_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3970_, 0, v___x_3968_);
                                leanh::lean_ctor_set(v___x_3970_, 1, v___x_3969_);
                                v___x_3971_ = l_Lean_MessageData_note(v___x_3970_);
                                v___x_3972_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3972_, 0, v_msg_3948_);
                                leanh::lean_ctor_set(v___x_3972_, 1, v___x_3971_);
                                v___x_3973_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3973_, 0, v___x_3972_);
                                return v___x_3973_;
                            } else {
                                v_val_3974_ = leanh::lean_ctor_get(v___x_3966_, 0);
                                v_isSharedCheck_4009_ =
                                    (!leanh::lean_is_exclusive(v___x_3966_)) as u8;
                                if v_isSharedCheck_4009_ == 0 {
                                    v___x_3976_ = v___x_3966_;
                                    v_isShared_3977_ = v_isSharedCheck_4009_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_3974_);
                                    leanh::lean_dec(v___x_3966_);
                                    v___x_3976_ = leanh::lean_box(0);
                                    v_isShared_3977_ = v_isSharedCheck_4009_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_3953_);
                    leanh::lean_dec(v_declHint_3949_);
                    v___x_4010_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4010_, 0, v_msg_3948_);
                    return v___x_4010_;
                }
            }
            1 => {
                v___x_3978_ = leanh::lean_box(0);
                v___x_3979_ = l_Lean_Environment_header(v_env_3953_);
                leanh::lean_dec_ref(v_env_3953_);
                v___x_3980_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3979_);
                v_mod_3981_ = lean_array_get(v___x_3978_, v___x_3980_, v_val_3974_);
                leanh::lean_dec(v_val_3974_);
                leanh::lean_dec_ref(v___x_3980_);
                v___x_3982_ = l_Lean_isPrivateName(v_declHint_3949_);
                leanh::lean_dec(v_declHint_3949_);
                if v___x_3982_ == 0 {
                    v___x_3983_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__11);
                    v___x_3984_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3984_, 0, v___x_3983_);
                    leanh::lean_ctor_set(v___x_3984_, 1, v_c_3965_);
                    v___x_3985_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__13);
                    v___x_3986_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3986_, 0, v___x_3984_);
                    leanh::lean_ctor_set(v___x_3986_, 1, v___x_3985_);
                    v___x_3987_ = l_Lean_MessageData_ofName(v_mod_3981_);
                    v___x_3988_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3988_, 0, v___x_3986_);
                    leanh::lean_ctor_set(v___x_3988_, 1, v___x_3987_);
                    v___x_3989_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__15);
                    v___x_3990_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3990_, 0, v___x_3988_);
                    leanh::lean_ctor_set(v___x_3990_, 1, v___x_3989_);
                    v___x_3991_ = l_Lean_MessageData_note(v___x_3990_);
                    v___x_3992_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3992_, 0, v_msg_3948_);
                    leanh::lean_ctor_set(v___x_3992_, 1, v___x_3991_);
                    if v_isShared_3977_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3976_, 0);
                        leanh::lean_ctor_set(v___x_3976_, 0, v___x_3992_);
                        v___x_3994_ = v___x_3976_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3995_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3995_, 0, v___x_3992_);
                        v___x_3994_ = v_reuseFailAlloc_3995_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3996_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__7);
                    v___x_3997_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3997_, 0, v___x_3996_);
                    leanh::lean_ctor_set(v___x_3997_, 1, v_c_3965_);
                    v___x_3998_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__17);
                    v___x_3999_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3999_, 0, v___x_3997_);
                    leanh::lean_ctor_set(v___x_3999_, 1, v___x_3998_);
                    v___x_4000_ = l_Lean_MessageData_ofName(v_mod_3981_);
                    v___x_4001_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4001_, 0, v___x_3999_);
                    leanh::lean_ctor_set(v___x_4001_, 1, v___x_4000_);
                    v___x_4002_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___closed__19);
                    v___x_4003_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4003_, 0, v___x_4001_);
                    leanh::lean_ctor_set(v___x_4003_, 1, v___x_4002_);
                    v___x_4004_ = l_Lean_MessageData_note(v___x_4003_);
                    v___x_4005_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4005_, 0, v_msg_3948_);
                    leanh::lean_ctor_set(v___x_4005_, 1, v___x_4004_);
                    if v_isShared_3977_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3976_, 0);
                        leanh::lean_ctor_set(v___x_3976_, 0, v___x_4005_);
                        v___x_4007_ = v___x_3976_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4008_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_4005_);
                        v___x_4007_ = v_reuseFailAlloc_4008_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3994_;
            }
            3 => {
                return v___x_4007_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg___boxed(
    mut v_msg_4011_: *mut leanh::LeanObject,
    mut v_declHint_4012_: *mut leanh::LeanObject,
    mut v___y_4013_: *mut leanh::LeanObject,
    mut v___y_4014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4015_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(v_msg_4011_, v_declHint_4012_, v___y_4013_);
    leanh::lean_dec(v___y_4013_);
    return v_res_4015_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32(
    mut v_msg_4016_: *mut leanh::LeanObject,
    mut v_declHint_4017_: *mut leanh::LeanObject,
    mut v___y_4018_: *mut leanh::LeanObject,
    mut v___y_4019_: *mut leanh::LeanObject,
    mut v___y_4020_: *mut leanh::LeanObject,
    mut v___y_4021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4027_: u8 = 0;
    let mut v___x_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4033_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4023_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(v_msg_4016_, v_declHint_4017_, v___y_4021_);
                v_a_4024_ = leanh::lean_ctor_get(v___x_4023_, 0);
                v_isSharedCheck_4033_ = (!leanh::lean_is_exclusive(v___x_4023_)) as u8;
                if v_isSharedCheck_4033_ == 0 {
                    v___x_4026_ = v___x_4023_;
                    v_isShared_4027_ = v_isSharedCheck_4033_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4024_);
                    leanh::lean_dec(v___x_4023_);
                    v___x_4026_ = leanh::lean_box(0);
                    v_isShared_4027_ = v_isSharedCheck_4033_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4028_ = l_Lean_unknownIdentifierMessageTag;
                v___x_4029_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4029_, 0, v___x_4028_);
                leanh::lean_ctor_set(v___x_4029_, 1, v_a_4024_);
                if v_isShared_4027_ == 0 {
                    leanh::lean_ctor_set(v___x_4026_, 0, v___x_4029_);
                    v___x_4031_ = v___x_4026_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4032_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4032_, 0, v___x_4029_);
                    v___x_4031_ = v_reuseFailAlloc_4032_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4031_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32___boxed(
    mut v_msg_4034_: *mut leanh::LeanObject,
    mut v_declHint_4035_: *mut leanh::LeanObject,
    mut v___y_4036_: *mut leanh::LeanObject,
    mut v___y_4037_: *mut leanh::LeanObject,
    mut v___y_4038_: *mut leanh::LeanObject,
    mut v___y_4039_: *mut leanh::LeanObject,
    mut v___y_4040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4041_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32(v_msg_4034_, v_declHint_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_);
    leanh::lean_dec(v___y_4039_);
    leanh::lean_dec_ref(v___y_4038_);
    leanh::lean_dec(v___y_4037_);
    leanh::lean_dec_ref(v___y_4036_);
    return v_res_4041_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(
    mut v_ref_4042_: *mut leanh::LeanObject,
    mut v_msg_4043_: *mut leanh::LeanObject,
    mut v_declHint_4044_: *mut leanh::LeanObject,
    mut v___y_4045_: *mut leanh::LeanObject,
    mut v___y_4046_: *mut leanh::LeanObject,
    mut v___y_4047_: *mut leanh::LeanObject,
    mut v___y_4048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4050_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32(v_msg_4043_, v_declHint_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
    v_a_4051_ = leanh::lean_ctor_get(v___x_4050_, 0);
    leanh::lean_inc(v_a_4051_);
    leanh::lean_dec_ref(v___x_4050_);
    v___x_4052_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(v_ref_4042_, v_a_4051_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
    return v___x_4052_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg___boxed(
    mut v_ref_4053_: *mut leanh::LeanObject,
    mut v_msg_4054_: *mut leanh::LeanObject,
    mut v_declHint_4055_: *mut leanh::LeanObject,
    mut v___y_4056_: *mut leanh::LeanObject,
    mut v___y_4057_: *mut leanh::LeanObject,
    mut v___y_4058_: *mut leanh::LeanObject,
    mut v___y_4059_: *mut leanh::LeanObject,
    mut v___y_4060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4061_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(v_ref_4053_, v_msg_4054_, v_declHint_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
    leanh::lean_dec(v___y_4059_);
    leanh::lean_dec_ref(v___y_4058_);
    leanh::lean_dec(v___y_4057_);
    leanh::lean_dec_ref(v___y_4056_);
    leanh::lean_dec(v_ref_4053_);
    return v_res_4061_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4063_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__0;
    v___x_4064_ = l_Lean_stringToMessageData(v___x_4063_);
    return v___x_4064_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(
    mut v_ref_4065_: *mut leanh::LeanObject,
    mut v_constName_4066_: *mut leanh::LeanObject,
    mut v___y_4067_: *mut leanh::LeanObject,
    mut v___y_4068_: *mut leanh::LeanObject,
    mut v___y_4069_: *mut leanh::LeanObject,
    mut v___y_4070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: u8 = 0;
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4072_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___closed__1);
    v___x_4073_ = 0;
    leanh::lean_inc(v_constName_4066_);
    v___x_4074_ = l_Lean_MessageData_ofConstName(v_constName_4066_, v___x_4073_);
    v___x_4075_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4075_, 0, v___x_4072_);
    leanh::lean_ctor_set(v___x_4075_, 1, v___x_4074_);
    v___x_4076_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once
        ),
        _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1,
    );
    v___x_4077_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4077_, 0, v___x_4075_);
    leanh::lean_ctor_set(v___x_4077_, 1, v___x_4076_);
    v___x_4078_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(v_ref_4065_, v___x_4077_, v_constName_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
    return v___x_4078_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg___boxed(
    mut v_ref_4079_: *mut leanh::LeanObject,
    mut v_constName_4080_: *mut leanh::LeanObject,
    mut v___y_4081_: *mut leanh::LeanObject,
    mut v___y_4082_: *mut leanh::LeanObject,
    mut v___y_4083_: *mut leanh::LeanObject,
    mut v___y_4084_: *mut leanh::LeanObject,
    mut v___y_4085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4086_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(v_ref_4079_, v_constName_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_);
    leanh::lean_dec(v___y_4084_);
    leanh::lean_dec_ref(v___y_4083_);
    leanh::lean_dec(v___y_4082_);
    leanh::lean_dec_ref(v___y_4081_);
    leanh::lean_dec(v_ref_4079_);
    return v_res_4086_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(
    mut v_constName_4087_: *mut leanh::LeanObject,
    mut v___y_4088_: *mut leanh::LeanObject,
    mut v___y_4089_: *mut leanh::LeanObject,
    mut v___y_4090_: *mut leanh::LeanObject,
    mut v___y_4091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_4093_ = leanh::lean_ctor_get(v___y_4090_, 5);
    v___x_4094_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(v_ref_4093_, v_constName_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
    return v___x_4094_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg___boxed(
    mut v_constName_4095_: *mut leanh::LeanObject,
    mut v___y_4096_: *mut leanh::LeanObject,
    mut v___y_4097_: *mut leanh::LeanObject,
    mut v___y_4098_: *mut leanh::LeanObject,
    mut v___y_4099_: *mut leanh::LeanObject,
    mut v___y_4100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4101_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(v_constName_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_);
    leanh::lean_dec(v___y_4099_);
    leanh::lean_dec_ref(v___y_4098_);
    leanh::lean_dec(v___y_4097_);
    leanh::lean_dec_ref(v___y_4096_);
    return v_res_4101_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5(
    mut v_constName_4102_: *mut leanh::LeanObject,
    mut v___y_4103_: *mut leanh::LeanObject,
    mut v___y_4104_: *mut leanh::LeanObject,
    mut v___y_4105_: *mut leanh::LeanObject,
    mut v___y_4106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: u8 = 0;
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4116_: u8 = 0;
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4108_ = lean_st_ref_get(v___y_4106_);
                v_env_4109_ = leanh::lean_ctor_get(v___x_4108_, 0);
                leanh::lean_inc_ref(v_env_4109_);
                leanh::lean_dec(v___x_4108_);
                v___x_4110_ = 0;
                leanh::lean_inc(v_constName_4102_);
                v___x_4111_ =
                    l_Lean_Environment_find_x3f(v_env_4109_, v_constName_4102_, v___x_4110_);
                if leanh::lean_obj_tag(v___x_4111_) == 0 {
                    v___x_4112_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(v_constName_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
                    return v___x_4112_;
                } else {
                    leanh::lean_dec(v_constName_4102_);
                    v_val_4113_ = leanh::lean_ctor_get(v___x_4111_, 0);
                    v_isSharedCheck_4120_ = (!leanh::lean_is_exclusive(v___x_4111_)) as u8;
                    if v_isSharedCheck_4120_ == 0 {
                        v___x_4115_ = v___x_4111_;
                        v_isShared_4116_ = v_isSharedCheck_4120_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4113_);
                        leanh::lean_dec(v___x_4111_);
                        v___x_4115_ = leanh::lean_box(0);
                        v_isShared_4116_ = v_isSharedCheck_4120_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4116_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4115_, 0);
                    v___x_4118_ = v___x_4115_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4119_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_val_4113_);
                    v___x_4118_ = v_reuseFailAlloc_4119_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4118_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5___boxed(
    mut v_constName_4121_: *mut leanh::LeanObject,
    mut v___y_4122_: *mut leanh::LeanObject,
    mut v___y_4123_: *mut leanh::LeanObject,
    mut v___y_4124_: *mut leanh::LeanObject,
    mut v___y_4125_: *mut leanh::LeanObject,
    mut v___y_4126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4127_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5(
        v_constName_4121_,
        v___y_4122_,
        v___y_4123_,
        v___y_4124_,
        v___y_4125_,
    );
    leanh::lean_dec(v___y_4125_);
    leanh::lean_dec_ref(v___y_4124_);
    leanh::lean_dec(v___y_4123_);
    leanh::lean_dec_ref(v___y_4122_);
    return v_res_4127_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(
    mut v_keys_4128_: *mut leanh::LeanObject,
    mut v_vals_4129_: *mut leanh::LeanObject,
    mut v_i_4130_: *mut leanh::LeanObject,
    mut v_k_4131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: u8 = 0;
    let mut v___x_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: u8 = 0;
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4132_ = lean_array_get_size(v_keys_4128_);
                v___x_4133_ = lean_nat_dec_lt(v_i_4130_, v___x_4132_);
                if v___x_4133_ == 0 {
                    leanh::lean_dec(v_i_4130_);
                    v___x_4134_ = leanh::lean_box(0);
                    return v___x_4134_;
                } else {
                    v_k_x27_4135_ = lean_array_fget_borrowed(v_keys_4128_, v_i_4130_);
                    v___x_4136_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_k_4131_, v_k_x27_4135_);
                    if v___x_4136_ == 0 {
                        v___x_4137_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4138_ = lean_nat_add(v_i_4130_, v___x_4137_);
                        leanh::lean_dec(v_i_4130_);
                        v_i_4130_ = v___x_4138_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4140_ = lean_array_fget_borrowed(v_vals_4129_, v_i_4130_);
                        leanh::lean_dec(v_i_4130_);
                        leanh::lean_inc(v___x_4140_);
                        v___x_4141_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4141_, 0, v___x_4140_);
                        return v___x_4141_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg___boxed(
    mut v_keys_4142_: *mut leanh::LeanObject,
    mut v_vals_4143_: *mut leanh::LeanObject,
    mut v_i_4144_: *mut leanh::LeanObject,
    mut v_k_4145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4146_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(v_keys_4142_, v_vals_4143_, v_i_4144_, v_k_4145_);
    leanh::lean_dec_ref(v_k_4145_);
    leanh::lean_dec_ref(v_vals_4143_);
    leanh::lean_dec_ref(v_keys_4142_);
    return v_res_4146_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(
    mut v_x_4147_: *mut leanh::LeanObject,
    mut v_x_4148_: usize,
    mut v_x_4149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: usize = 0;
    let mut v___x_4153_: usize = 0;
    let mut v___x_4154_: usize = 0;
    let mut v_j_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: u8 = 0;
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: usize = 0;
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4147_) == 0 {
                    v_es_4150_ = leanh::lean_ctor_get(v_x_4147_, 0);
                    v___x_4151_ = leanh::lean_box(2);
                    v___x_4152_ = 5usize;
                    v___x_4153_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__1);
                    v___x_4154_ = lean_usize_land(v_x_4148_, v___x_4153_);
                    v_j_4155_ = lean_usize_to_nat(v___x_4154_);
                    v___x_4156_ = lean_array_get_borrowed(v___x_4151_, v_es_4150_, v_j_4155_);
                    leanh::lean_dec(v_j_4155_);
                    match leanh::lean_obj_tag(v___x_4156_) {
                        0 => {
                            v_key_4157_ = leanh::lean_ctor_get(v___x_4156_, 0);
                            v_val_4158_ = leanh::lean_ctor_get(v___x_4156_, 1);
                            v___x_4159_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_4149_, v_key_4157_);
                            if v___x_4159_ == 0 {
                                v___x_4160_ = leanh::lean_box(0);
                                return v___x_4160_;
                            } else {
                                leanh::lean_inc(v_val_4158_);
                                v___x_4161_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4161_, 0, v_val_4158_);
                                return v___x_4161_;
                            }
                        }
                        1 => {
                            v_node_4162_ = leanh::lean_ctor_get(v___x_4156_, 0);
                            v___x_4163_ = lean_usize_shift_right(v_x_4148_, v___x_4152_);
                            v_x_4147_ = v_node_4162_;
                            v_x_4148_ = v___x_4163_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4165_ = leanh::lean_box(0);
                            return v___x_4165_;
                        }
                    }
                } else {
                    v_ks_4166_ = leanh::lean_ctor_get(v_x_4147_, 0);
                    v_vs_4167_ = leanh::lean_ctor_get(v_x_4147_, 1);
                    v___x_4168_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4169_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(v_ks_4166_, v_vs_4167_, v___x_4168_, v_x_4149_);
                    return v___x_4169_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg___boxed(
    mut v_x_4170_: *mut leanh::LeanObject,
    mut v_x_4171_: *mut leanh::LeanObject,
    mut v_x_4172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_23197__boxed_4173_: usize = 0;
    let mut v_res_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_23197__boxed_4173_ = leanh::lean_unbox_usize(v_x_4171_);
    leanh::lean_dec(v_x_4171_);
    v_res_4174_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_4170_, v_x_23197__boxed_4173_, v_x_4172_);
    leanh::lean_dec_ref(v_x_4172_);
    leanh::lean_dec_ref(v_x_4170_);
    return v_res_4174_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(
    mut v_x_4175_: *mut leanh::LeanObject,
    mut v_x_4176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4177_: u64 = 0;
    let mut v___x_4178_: usize = 0;
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4177_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_4176_);
    v___x_4178_ = lean_uint64_to_usize(v___x_4177_);
    v___x_4179_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_4175_, v___x_4178_, v_x_4176_);
    return v___x_4179_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg___boxed(
    mut v_x_4180_: *mut leanh::LeanObject,
    mut v_x_4181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4182_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(
            v_x_4180_, v_x_4181_,
        );
    leanh::lean_dec_ref(v_x_4181_);
    leanh::lean_dec_ref(v_x_4180_);
    return v_res_4182_;
}
pub unsafe fn _init_l_Lean_Meta_mkSparseCasesOn___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4185_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6;
    v___x_4186_ = leanh::lean_unsigned_to_nat(42);
    v___x_4187_ = leanh::lean_unsigned_to_nat(81);
    v___x_4188_ = l_Lean_Meta_mkSparseCasesOn___closed__1;
    v___x_4189_ = l_Lean_Meta_mkSparseCasesOn___closed__0;
    v___x_4190_ = l_mkPanicMessageWithDecl(
        v___x_4189_,
        v___x_4188_,
        v___x_4187_,
        v___x_4186_,
        v___x_4185_,
    );
    return v___x_4190_;
}
pub unsafe fn _init_l_Lean_Meta_mkSparseCasesOn___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4192_ = l_Lean_Meta_mkSparseCasesOn___closed__3;
    v___x_4193_ = l_Lean_stringToMessageData(v___x_4192_);
    return v___x_4193_;
}
pub unsafe fn _init_l_Lean_Meta_mkSparseCasesOn___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4194_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0;
    v___x_4195_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0;
    v___x_4196_ = l_Lean_PersistentHashMap_instInhabited(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4195_,
        v___x_4194_,
    );
    return v___x_4196_;
}
pub unsafe fn _init_l_Lean_Meta_mkSparseCasesOn___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4201_ = l_Lean_Meta_mkSparseCasesOn___closed__8;
    v___x_4202_ = l_Lean_stringToMessageData(v___x_4201_);
    return v___x_4202_;
}
pub unsafe fn l_Lean_Meta_mkSparseCasesOn(
    mut v_indName_4203_: *mut leanh::LeanObject,
    mut v_ctors_4204_: *mut leanh::LeanObject,
    mut v_a_4205_: *mut leanh::LeanObject,
    mut v_a_4206_: *mut leanh::LeanObject,
    mut v_a_4207_: *mut leanh::LeanObject,
    mut v_a_4208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_4213_: u8 = 0;
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: u8 = 0;
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4249_: u8 = 0;
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4264_: u8 = 0;
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4277_: u8 = 0;
    let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4294_: u8 = 0;
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4306_: u8 = 0;
    let mut v___x_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4321_: u8 = 0;
    let mut v_numParams_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4344_: u8 = 0;
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4351_: u8 = 0;
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4355_: u8 = 0;
    let mut v_unused_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4360_: u8 = 0;
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4364_: u8 = 0;
    let mut v_reuseFailAlloc_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4366_: u8 = 0;
    let mut v_unused_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4369_: u8 = 0;
    let mut v_unused_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4372_: u8 = 0;
    let mut v_unused_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4375_: u8 = 0;
    let mut v_unused_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4378_: u8 = 0;
    let mut v_unused_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4381_: u8 = 0;
    let mut v_unused_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4386_: u8 = 0;
    let mut v___x_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4390_: u8 = 0;
    let mut v_reuseFailAlloc_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4392_: u8 = 0;
    let mut v_a_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4396_: u8 = 0;
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4400_: u8 = 0;
    let mut v_a_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4404_: u8 = 0;
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4408_: u8 = 0;
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: u8 = 0;
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4446_: u8 = 0;
    let mut v___x_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4450_: u8 = 0;
    let mut v_a_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4454_: u8 = 0;
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4458_: u8 = 0;
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4461_: u8 = 0;
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4471_: u8 = 0;
    let mut v___x_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4475_: u8 = 0;
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4482_: usize = 0;
    let mut v___x_4483_: usize = 0;
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: u8 = 0;
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4497_: u8 = 0;
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4501_: u8 = 0;
    let mut v_a_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4505_: u8 = 0;
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4509_: u8 = 0;
    let mut v_a_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4513_: u8 = 0;
    let mut v___x_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4517_: u8 = 0;
    let mut v_isExporting_4518_: u8 = 0;
    let mut v___x_4519_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4210_ = lean_st_ref_get(v_a_4208_);
                v_env_4211_ = leanh::lean_ctor_get(v___x_4210_, 0);
                leanh::lean_inc_ref(v_env_4211_);
                leanh::lean_dec(v___x_4210_);
                v___x_4212_ = l_Lean_Environment_header(v_env_4211_);
                v_isModule_4213_ = leanh::lean_ctor_get_uint8(
                    v___x_4212_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 4) as u32,
                );
                leanh::lean_dec_ref(v___x_4212_);
                v___x_4214_ = l_Lean_instInhabitedExpr;
                v___x_4459_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkSparseCasesOn___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Meta_mkSparseCasesOn___closed__5_once),
                    _init_l_Lean_Meta_mkSparseCasesOn___closed__5,
                );
                if v_isModule_4213_ == 0 {
                    v___y_4461_ = v_isModule_4213_;
                    state = 31;
                    continue;
                } else {
                    v_isExporting_4518_ = leanh::lean_ctor_get_uint8(
                        v_env_4211_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_4518_ == 0 {
                        v___y_4461_ = v_isModule_4213_;
                        state = 31;
                        continue;
                    } else {
                        v___x_4519_ = 0;
                        v___y_4461_ = v___x_4519_;
                        state = 31;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4233_ = l_Lean_ConstantInfo_levelParams(v___y_4223_);
                if leanh::lean_obj_tag(v___x_4233_) == 1 {
                    v_tail_4234_ = leanh::lean_ctor_get(v___x_4233_, 1);
                    leanh::lean_inc(v_tail_4234_);
                    v___x_4235_ = leanh::lean_box(0);
                    v___x_4236_ = l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__6(
                        v_tail_4234_,
                        v___x_4235_,
                    );
                    leanh::lean_inc_ref(v_ctors_4204_);
                    v___f_4237_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_mkSparseCasesOn___lam__2___boxed as *mut core::ffi::c_void,
                        16,
                        9,
                    );
                    leanh::lean_closure_set(v___f_4237_, 0, v___y_4217_);
                    leanh::lean_closure_set(v___f_4237_, 1, v___x_4214_);
                    leanh::lean_closure_set(v___f_4237_, 2, v___y_4219_);
                    leanh::lean_closure_set(v___f_4237_, 3, v_ctors_4204_);
                    leanh::lean_closure_set(v___f_4237_, 4, v___y_4221_);
                    leanh::lean_closure_set(v___f_4237_, 5, v___x_4236_);
                    leanh::lean_closure_set(v___f_4237_, 6, v___y_4216_);
                    leanh::lean_closure_set(v___f_4237_, 7, v___y_4218_);
                    leanh::lean_closure_set(v___f_4237_, 8, v___y_4220_);
                    v___x_4238_ = l_Lean_ConstantInfo_type(v___y_4223_);
                    leanh::lean_dec_ref(v___y_4223_);
                    v___x_4239_ = 0;
                    v___x_4240_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__11___redArg(v___x_4238_, v___f_4237_, v___x_4239_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
                    if leanh::lean_obj_tag(v___x_4240_) == 0 {
                        v_a_4241_ = leanh::lean_ctor_get(v___x_4240_, 0);
                        leanh::lean_inc_n(v_a_4241_, 2);
                        leanh::lean_dec_ref_known(v___x_4240_, 1);
                        leanh::lean_inc(v___y_4232_);
                        leanh::lean_inc_ref(v___y_4231_);
                        leanh::lean_inc(v___y_4230_);
                        leanh::lean_inc_ref(v___y_4229_);
                        v___x_4242_ = lean_infer_type(
                            v_a_4241_,
                            v___y_4229_,
                            v___y_4230_,
                            v___y_4231_,
                            v___y_4232_,
                        );
                        if leanh::lean_obj_tag(v___x_4242_) == 0 {
                            v_a_4243_ = leanh::lean_ctor_get(v___x_4242_, 0);
                            leanh::lean_inc(v_a_4243_);
                            leanh::lean_dec_ref_known(v___x_4242_, 1);
                            v___x_4244_ = leanh::lean_box(1);
                            leanh::lean_inc(v___y_4224_);
                            v___x_4245_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___y_4224_, v___x_4233_, v_a_4243_, v_a_4241_, v___x_4244_, v___y_4232_);
                            v_a_4246_ = leanh::lean_ctor_get(v___x_4245_, 0);
                            v_isSharedCheck_4392_ =
                                (!leanh::lean_is_exclusive(v___x_4245_)) as u8;
                            if v_isSharedCheck_4392_ == 0 {
                                v___x_4248_ = v___x_4245_;
                                v_isShared_4249_ = v_isSharedCheck_4392_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4246_);
                                leanh::lean_dec(v___x_4245_);
                                v___x_4248_ = leanh::lean_box(0);
                                v_isShared_4249_ = v_isSharedCheck_4392_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_4241_);
                            leanh::lean_dec_ref_known(v___x_4233_, 2);
                            leanh::lean_dec_ref(v___y_4228_);
                            leanh::lean_dec_ref(v___y_4227_);
                            leanh::lean_dec(v___y_4226_);
                            leanh::lean_dec(v___y_4224_);
                            leanh::lean_dec_ref(v_ctors_4204_);
                            leanh::lean_dec(v_indName_4203_);
                            v_a_4393_ = leanh::lean_ctor_get(v___x_4242_, 0);
                            v_isSharedCheck_4400_ =
                                (!leanh::lean_is_exclusive(v___x_4242_)) as u8;
                            if v_isSharedCheck_4400_ == 0 {
                                v___x_4395_ = v___x_4242_;
                                v_isShared_4396_ = v_isSharedCheck_4400_;
                                state = 22;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4393_);
                                leanh::lean_dec(v___x_4242_);
                                v___x_4395_ = leanh::lean_box(0);
                                v_isShared_4396_ = v_isSharedCheck_4400_;
                                state = 22;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_4233_, 2);
                        leanh::lean_dec_ref(v___y_4228_);
                        leanh::lean_dec_ref(v___y_4227_);
                        leanh::lean_dec(v___y_4226_);
                        leanh::lean_dec(v___y_4224_);
                        leanh::lean_dec_ref(v_ctors_4204_);
                        leanh::lean_dec(v_indName_4203_);
                        v_a_4401_ = leanh::lean_ctor_get(v___x_4240_, 0);
                        v_isSharedCheck_4408_ =
                            (!leanh::lean_is_exclusive(v___x_4240_)) as u8;
                        if v_isSharedCheck_4408_ == 0 {
                            v___x_4403_ = v___x_4240_;
                            v_isShared_4404_ = v_isSharedCheck_4408_;
                            state = 24;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4401_);
                            leanh::lean_dec(v___x_4240_);
                            v___x_4403_ = leanh::lean_box(0);
                            v_isShared_4404_ = v_isSharedCheck_4408_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_4233_);
                    leanh::lean_dec_ref(v___y_4228_);
                    leanh::lean_dec_ref(v___y_4227_);
                    leanh::lean_dec(v___y_4226_);
                    leanh::lean_dec(v___y_4224_);
                    leanh::lean_dec_ref(v___y_4223_);
                    leanh::lean_dec(v___y_4221_);
                    leanh::lean_dec(v___y_4220_);
                    leanh::lean_dec(v___y_4219_);
                    leanh::lean_dec(v___y_4218_);
                    leanh::lean_dec(v___y_4217_);
                    leanh::lean_dec_ref(v___y_4216_);
                    leanh::lean_dec_ref(v_ctors_4204_);
                    leanh::lean_dec(v_indName_4203_);
                    v___x_4409_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkSparseCasesOn___closed__2),
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkSparseCasesOn___closed__2_once),
                        _init_l_Lean_Meta_mkSparseCasesOn___closed__2,
                    );
                    v___x_4410_ = l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__16(
                        v___x_4409_,
                        v___y_4229_,
                        v___y_4230_,
                        v___y_4231_,
                        v___y_4232_,
                    );
                    return v___x_4410_;
                }
            }
            2 => {
                if v_isShared_4249_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4248_, 1);
                    v___x_4251_ = v___x_4248_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4391_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 0, v_a_4246_);
                    v___x_4251_ = v_reuseFailAlloc_4391_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4252_ = l_Lean_addDecl(v___x_4251_, v___x_4239_, v___y_4231_, v___y_4232_);
                if leanh::lean_obj_tag(v___x_4252_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4252_, 1);
                    v___x_4253_ = lean_st_ref_take(v___y_4232_);
                    v_env_4254_ = leanh::lean_ctor_get(v___x_4253_, 0);
                    v_nextMacroScope_4255_ = leanh::lean_ctor_get(v___x_4253_, 1);
                    v_ngen_4256_ = leanh::lean_ctor_get(v___x_4253_, 2);
                    v_auxDeclNGen_4257_ = leanh::lean_ctor_get(v___x_4253_, 3);
                    v_traceState_4258_ = leanh::lean_ctor_get(v___x_4253_, 4);
                    v_messages_4259_ = leanh::lean_ctor_get(v___x_4253_, 6);
                    v_infoState_4260_ = leanh::lean_ctor_get(v___x_4253_, 7);
                    v_snapshotTasks_4261_ = leanh::lean_ctor_get(v___x_4253_, 8);
                    v_isSharedCheck_4381_ = (!leanh::lean_is_exclusive(v___x_4253_)) as u8;
                    if v_isSharedCheck_4381_ == 0 {
                        v_unused_4382_ = leanh::lean_ctor_get(v___x_4253_, 5);
                        leanh::lean_dec(v_unused_4382_);
                        v___x_4263_ = v___x_4253_;
                        v_isShared_4264_ = v_isSharedCheck_4381_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_4261_);
                        leanh::lean_inc(v_infoState_4260_);
                        leanh::lean_inc(v_messages_4259_);
                        leanh::lean_inc(v_traceState_4258_);
                        leanh::lean_inc(v_auxDeclNGen_4257_);
                        leanh::lean_inc(v_ngen_4256_);
                        leanh::lean_inc(v_nextMacroScope_4255_);
                        leanh::lean_inc(v_env_4254_);
                        leanh::lean_dec(v___x_4253_);
                        v___x_4263_ = leanh::lean_box(0);
                        v_isShared_4264_ = v_isSharedCheck_4381_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_4228_);
                    leanh::lean_dec_ref(v___y_4227_);
                    leanh::lean_dec(v___y_4226_);
                    leanh::lean_dec(v___y_4224_);
                    leanh::lean_dec_ref(v_ctors_4204_);
                    leanh::lean_dec(v_indName_4203_);
                    v_a_4383_ = leanh::lean_ctor_get(v___x_4252_, 0);
                    v_isSharedCheck_4390_ = (!leanh::lean_is_exclusive(v___x_4252_)) as u8;
                    if v_isSharedCheck_4390_ == 0 {
                        v___x_4385_ = v___x_4252_;
                        v_isShared_4386_ = v_isSharedCheck_4390_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4383_);
                        leanh::lean_dec(v___x_4252_);
                        v___x_4385_ = leanh::lean_box(0);
                        v_isShared_4386_ = v_isSharedCheck_4390_;
                        state = 20;
                        continue;
                    }
                }
            }
            4 => {
                leanh::lean_inc_ref(v___y_4225_);
                v___x_4265_ = l_Lean_EnvExtension_modifyState___redArg(
                    v___y_4225_,
                    v_env_4254_,
                    v___y_4227_,
                    v___y_4222_,
                    v___y_4226_,
                );
                v___x_4266_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__2);
                if v_isShared_4264_ == 0 {
                    leanh::lean_ctor_set(v___x_4263_, 5, v___x_4266_);
                    leanh::lean_ctor_set(v___x_4263_, 0, v___x_4265_);
                    v___x_4268_ = v___x_4263_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4380_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4380_, 0, v___x_4265_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4380_, 1, v_nextMacroScope_4255_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4380_, 2, v_ngen_4256_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4380_, 3, v_auxDeclNGen_4257_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4380_, 4, v_traceState_4258_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4380_, 5, v___x_4266_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4380_, 6, v_messages_4259_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4380_, 7, v_infoState_4260_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4380_, 8, v_snapshotTasks_4261_);
                    v___x_4268_ = v_reuseFailAlloc_4380_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4269_ = lean_st_ref_set(v___y_4232_, v___x_4268_);
                v___x_4270_ = lean_st_ref_take(v___y_4230_);
                v_mctx_4271_ = leanh::lean_ctor_get(v___x_4270_, 0);
                v_zetaDeltaFVarIds_4272_ = leanh::lean_ctor_get(v___x_4270_, 2);
                v_postponed_4273_ = leanh::lean_ctor_get(v___x_4270_, 3);
                v_diag_4274_ = leanh::lean_ctor_get(v___x_4270_, 4);
                v_isSharedCheck_4378_ = (!leanh::lean_is_exclusive(v___x_4270_)) as u8;
                if v_isSharedCheck_4378_ == 0 {
                    v_unused_4379_ = leanh::lean_ctor_get(v___x_4270_, 1);
                    leanh::lean_dec(v_unused_4379_);
                    v___x_4276_ = v___x_4270_;
                    v_isShared_4277_ = v_isSharedCheck_4378_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4274_);
                    leanh::lean_inc(v_postponed_4273_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4272_);
                    leanh::lean_inc(v_mctx_4271_);
                    leanh::lean_dec(v___x_4270_);
                    v___x_4276_ = leanh::lean_box(0);
                    v_isShared_4277_ = v_isSharedCheck_4378_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4278_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg___closed__3);
                if v_isShared_4277_ == 0 {
                    leanh::lean_ctor_set(v___x_4276_, 1, v___x_4278_);
                    v___x_4280_ = v___x_4276_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4377_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_mctx_4271_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4377_, 1, v___x_4278_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4377_,
                        2,
                        v_zetaDeltaFVarIds_4272_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4377_, 3, v_postponed_4273_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4377_, 4, v_diag_4274_);
                    v___x_4280_ = v_reuseFailAlloc_4377_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4281_ = lean_st_ref_set(v___y_4230_, v___x_4280_);
                leanh::lean_inc(v___y_4224_);
                v___x_4282_ =
                    l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15(
                        v___y_4224_,
                        v___y_4229_,
                        v___y_4230_,
                        v___y_4231_,
                        v___y_4232_,
                    );
                leanh::lean_dec_ref(v___x_4282_);
                v___x_4283_ = lean_st_ref_take(v___y_4232_);
                v_env_4284_ = leanh::lean_ctor_get(v___x_4283_, 0);
                v_nextMacroScope_4285_ = leanh::lean_ctor_get(v___x_4283_, 1);
                v_ngen_4286_ = leanh::lean_ctor_get(v___x_4283_, 2);
                v_auxDeclNGen_4287_ = leanh::lean_ctor_get(v___x_4283_, 3);
                v_traceState_4288_ = leanh::lean_ctor_get(v___x_4283_, 4);
                v_messages_4289_ = leanh::lean_ctor_get(v___x_4283_, 6);
                v_infoState_4290_ = leanh::lean_ctor_get(v___x_4283_, 7);
                v_snapshotTasks_4291_ = leanh::lean_ctor_get(v___x_4283_, 8);
                v_isSharedCheck_4375_ = (!leanh::lean_is_exclusive(v___x_4283_)) as u8;
                if v_isSharedCheck_4375_ == 0 {
                    v_unused_4376_ = leanh::lean_ctor_get(v___x_4283_, 5);
                    leanh::lean_dec(v_unused_4376_);
                    v___x_4293_ = v___x_4283_;
                    v_isShared_4294_ = v_isSharedCheck_4375_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4291_);
                    leanh::lean_inc(v_infoState_4290_);
                    leanh::lean_inc(v_messages_4289_);
                    leanh::lean_inc(v_traceState_4288_);
                    leanh::lean_inc(v_auxDeclNGen_4287_);
                    leanh::lean_inc(v_ngen_4286_);
                    leanh::lean_inc(v_nextMacroScope_4285_);
                    leanh::lean_inc(v_env_4284_);
                    leanh::lean_dec(v___x_4283_);
                    v___x_4293_ = leanh::lean_box(0);
                    v_isShared_4294_ = v_isSharedCheck_4375_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                leanh::lean_inc(v___y_4224_);
                v___x_4295_ = l_Lean_markSparseCasesOn(v_env_4284_, v___y_4224_);
                if v_isShared_4294_ == 0 {
                    leanh::lean_ctor_set(v___x_4293_, 5, v___x_4266_);
                    leanh::lean_ctor_set(v___x_4293_, 0, v___x_4295_);
                    v___x_4297_ = v___x_4293_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4374_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4374_, 0, v___x_4295_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4374_, 1, v_nextMacroScope_4285_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4374_, 2, v_ngen_4286_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4374_, 3, v_auxDeclNGen_4287_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4374_, 4, v_traceState_4288_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4374_, 5, v___x_4266_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4374_, 6, v_messages_4289_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4374_, 7, v_infoState_4290_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4374_, 8, v_snapshotTasks_4291_);
                    v___x_4297_ = v_reuseFailAlloc_4374_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4298_ = lean_st_ref_set(v___y_4232_, v___x_4297_);
                v___x_4299_ = lean_st_ref_take(v___y_4230_);
                v_mctx_4300_ = leanh::lean_ctor_get(v___x_4299_, 0);
                v_zetaDeltaFVarIds_4301_ = leanh::lean_ctor_get(v___x_4299_, 2);
                v_postponed_4302_ = leanh::lean_ctor_get(v___x_4299_, 3);
                v_diag_4303_ = leanh::lean_ctor_get(v___x_4299_, 4);
                v_isSharedCheck_4372_ = (!leanh::lean_is_exclusive(v___x_4299_)) as u8;
                if v_isSharedCheck_4372_ == 0 {
                    v_unused_4373_ = leanh::lean_ctor_get(v___x_4299_, 1);
                    leanh::lean_dec(v_unused_4373_);
                    v___x_4305_ = v___x_4299_;
                    v_isShared_4306_ = v_isSharedCheck_4372_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4303_);
                    leanh::lean_inc(v_postponed_4302_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4301_);
                    leanh::lean_inc(v_mctx_4300_);
                    leanh::lean_dec(v___x_4299_);
                    v___x_4305_ = leanh::lean_box(0);
                    v_isShared_4306_ = v_isSharedCheck_4372_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_4306_ == 0 {
                    leanh::lean_ctor_set(v___x_4305_, 1, v___x_4278_);
                    v___x_4308_ = v___x_4305_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4371_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_mctx_4300_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 1, v___x_4278_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4371_,
                        2,
                        v_zetaDeltaFVarIds_4301_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 3, v_postponed_4302_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 4, v_diag_4303_);
                    v___x_4308_ = v_reuseFailAlloc_4371_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_4309_ = lean_st_ref_set(v___y_4230_, v___x_4308_);
                v___x_4310_ = lean_st_ref_take(v___y_4232_);
                v_env_4311_ = leanh::lean_ctor_get(v___x_4310_, 0);
                v_nextMacroScope_4312_ = leanh::lean_ctor_get(v___x_4310_, 1);
                v_ngen_4313_ = leanh::lean_ctor_get(v___x_4310_, 2);
                v_auxDeclNGen_4314_ = leanh::lean_ctor_get(v___x_4310_, 3);
                v_traceState_4315_ = leanh::lean_ctor_get(v___x_4310_, 4);
                v_messages_4316_ = leanh::lean_ctor_get(v___x_4310_, 6);
                v_infoState_4317_ = leanh::lean_ctor_get(v___x_4310_, 7);
                v_snapshotTasks_4318_ = leanh::lean_ctor_get(v___x_4310_, 8);
                v_isSharedCheck_4369_ = (!leanh::lean_is_exclusive(v___x_4310_)) as u8;
                if v_isSharedCheck_4369_ == 0 {
                    v_unused_4370_ = leanh::lean_ctor_get(v___x_4310_, 5);
                    leanh::lean_dec(v_unused_4370_);
                    v___x_4320_ = v___x_4310_;
                    v_isShared_4321_ = v_isSharedCheck_4369_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4318_);
                    leanh::lean_inc(v_infoState_4317_);
                    leanh::lean_inc(v_messages_4316_);
                    leanh::lean_inc(v_traceState_4315_);
                    leanh::lean_inc(v_auxDeclNGen_4314_);
                    leanh::lean_inc(v_ngen_4313_);
                    leanh::lean_inc(v_nextMacroScope_4312_);
                    leanh::lean_inc(v_env_4311_);
                    leanh::lean_dec(v___x_4310_);
                    v___x_4320_ = leanh::lean_box(0);
                    v_isShared_4321_ = v_isSharedCheck_4369_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_numParams_4322_ = leanh::lean_ctor_get(v___y_4228_, 1);
                leanh::lean_inc(v_numParams_4322_);
                v_numIndices_4323_ = leanh::lean_ctor_get(v___y_4228_, 2);
                leanh::lean_inc(v_numIndices_4323_);
                leanh::lean_dec_ref(v___y_4228_);
                v___x_4324_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
                v___x_4325_ = leanh::lean_unsigned_to_nat(1);
                v___x_4326_ = lean_nat_add(v_numParams_4322_, v___x_4325_);
                leanh::lean_dec(v_numParams_4322_);
                v___x_4327_ = lean_nat_add(v___x_4326_, v_numIndices_4323_);
                leanh::lean_dec(v_numIndices_4323_);
                leanh::lean_dec(v___x_4326_);
                v___x_4328_ = lean_nat_add(v___x_4327_, v___x_4325_);
                v___x_4329_ = lean_array_get_size(v_ctors_4204_);
                v___x_4330_ = lean_nat_add(v___x_4328_, v___x_4329_);
                leanh::lean_dec(v___x_4328_);
                v___x_4331_ = lean_nat_add(v___x_4330_, v___x_4325_);
                leanh::lean_dec(v___x_4330_);
                v___x_4332_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4332_, 0, v_indName_4203_);
                leanh::lean_ctor_set(v___x_4332_, 1, v___x_4327_);
                leanh::lean_ctor_set(v___x_4332_, 2, v___x_4331_);
                leanh::lean_ctor_set(v___x_4332_, 3, v_ctors_4204_);
                leanh::lean_inc(v___y_4224_);
                v___x_4333_ = l_Lean_MapDeclarationExtension_insert___redArg(
                    v___x_4324_,
                    v_env_4311_,
                    v___y_4224_,
                    v___x_4332_,
                );
                if v_isShared_4321_ == 0 {
                    leanh::lean_ctor_set(v___x_4320_, 5, v___x_4266_);
                    leanh::lean_ctor_set(v___x_4320_, 0, v___x_4333_);
                    v___x_4335_ = v___x_4320_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4368_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 0, v___x_4333_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 1, v_nextMacroScope_4312_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 2, v_ngen_4313_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 3, v_auxDeclNGen_4314_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 4, v_traceState_4315_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 5, v___x_4266_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 6, v_messages_4316_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 7, v_infoState_4317_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 8, v_snapshotTasks_4318_);
                    v___x_4335_ = v_reuseFailAlloc_4368_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_4336_ = lean_st_ref_set(v___y_4232_, v___x_4335_);
                v___x_4337_ = lean_st_ref_take(v___y_4230_);
                v_mctx_4338_ = leanh::lean_ctor_get(v___x_4337_, 0);
                v_zetaDeltaFVarIds_4339_ = leanh::lean_ctor_get(v___x_4337_, 2);
                v_postponed_4340_ = leanh::lean_ctor_get(v___x_4337_, 3);
                v_diag_4341_ = leanh::lean_ctor_get(v___x_4337_, 4);
                v_isSharedCheck_4366_ = (!leanh::lean_is_exclusive(v___x_4337_)) as u8;
                if v_isSharedCheck_4366_ == 0 {
                    v_unused_4367_ = leanh::lean_ctor_get(v___x_4337_, 1);
                    leanh::lean_dec(v_unused_4367_);
                    v___x_4343_ = v___x_4337_;
                    v_isShared_4344_ = v_isSharedCheck_4366_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4341_);
                    leanh::lean_inc(v_postponed_4340_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4339_);
                    leanh::lean_inc(v_mctx_4338_);
                    leanh::lean_dec(v___x_4337_);
                    v___x_4343_ = leanh::lean_box(0);
                    v_isShared_4344_ = v_isSharedCheck_4366_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_4344_ == 0 {
                    leanh::lean_ctor_set(v___x_4343_, 1, v___x_4278_);
                    v___x_4346_ = v___x_4343_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4365_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_mctx_4338_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4365_, 1, v___x_4278_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4365_,
                        2,
                        v_zetaDeltaFVarIds_4339_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4365_, 3, v_postponed_4340_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4365_, 4, v_diag_4341_);
                    v___x_4346_ = v_reuseFailAlloc_4365_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_4347_ = lean_st_ref_set(v___y_4230_, v___x_4346_);
                leanh::lean_inc(v___y_4224_);
                v___x_4348_ =
                    l_Lean_enableRealizationsForConst(v___y_4224_, v___y_4231_, v___y_4232_);
                if leanh::lean_obj_tag(v___x_4348_) == 0 {
                    v_isSharedCheck_4355_ = (!leanh::lean_is_exclusive(v___x_4348_)) as u8;
                    if v_isSharedCheck_4355_ == 0 {
                        v_unused_4356_ = leanh::lean_ctor_get(v___x_4348_, 0);
                        leanh::lean_dec(v_unused_4356_);
                        v___x_4350_ = v___x_4348_;
                        v_isShared_4351_ = v_isSharedCheck_4355_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4348_);
                        v___x_4350_ = leanh::lean_box(0);
                        v_isShared_4351_ = v_isSharedCheck_4355_;
                        state = 16;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_4224_);
                    v_a_4357_ = leanh::lean_ctor_get(v___x_4348_, 0);
                    v_isSharedCheck_4364_ = (!leanh::lean_is_exclusive(v___x_4348_)) as u8;
                    if v_isSharedCheck_4364_ == 0 {
                        v___x_4359_ = v___x_4348_;
                        v_isShared_4360_ = v_isSharedCheck_4364_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4357_);
                        leanh::lean_dec(v___x_4348_);
                        v___x_4359_ = leanh::lean_box(0);
                        v_isShared_4360_ = v_isSharedCheck_4364_;
                        state = 18;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_4351_ == 0 {
                    leanh::lean_ctor_set(v___x_4350_, 0, v___y_4224_);
                    v___x_4353_ = v___x_4350_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4354_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4354_, 0, v___y_4224_);
                    v___x_4353_ = v_reuseFailAlloc_4354_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4353_;
            }
            18 => {
                if v_isShared_4360_ == 0 {
                    v___x_4362_ = v___x_4359_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4363_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
                    v___x_4362_ = v_reuseFailAlloc_4363_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4362_;
            }
            20 => {
                if v_isShared_4386_ == 0 {
                    v___x_4388_ = v___x_4385_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4389_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_a_4383_);
                    v___x_4388_ = v_reuseFailAlloc_4389_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4388_;
            }
            22 => {
                if v_isShared_4396_ == 0 {
                    v___x_4398_ = v___x_4395_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4399_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_a_4393_);
                    v___x_4398_ = v_reuseFailAlloc_4399_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_4398_;
            }
            24 => {
                if v_isShared_4404_ == 0 {
                    v___x_4406_ = v___x_4403_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4407_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_a_4401_);
                    v___x_4406_ = v_reuseFailAlloc_4407_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_4406_;
            }
            26 => {
                leanh::lean_inc(v_indName_4203_);
                v___x_4425_ = l_Lean_mkCasesOnName(v_indName_4203_);
                leanh::lean_inc(v___x_4425_);
                v___x_4426_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5(
                    v___x_4425_,
                    v___y_4421_,
                    v___y_4422_,
                    v___y_4423_,
                    v___y_4424_,
                );
                if leanh::lean_obj_tag(v___x_4426_) == 0 {
                    v_toConstantVal_4427_ = leanh::lean_ctor_get(v___y_4420_, 0);
                    v_a_4428_ = leanh::lean_ctor_get(v___x_4426_, 0);
                    leanh::lean_inc(v_a_4428_);
                    leanh::lean_dec_ref_known(v___x_4426_, 1);
                    v_levelParams_4429_ = leanh::lean_ctor_get(v_toConstantVal_4427_, 1);
                    leanh::lean_inc(v_indName_4203_);
                    v___x_4430_ = l_mkCtorIdxName(v_indName_4203_);
                    v___x_4431_ = l_Lean_ConstantInfo_levelParams(v_a_4428_);
                    v___x_4432_ = l_List_lengthTR___redArg(v___x_4431_);
                    leanh::lean_dec(v___x_4431_);
                    v___x_4433_ = l_List_lengthTR___redArg(v_levelParams_4429_);
                    v___x_4434_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4435_ = lean_nat_add(v___x_4433_, v___x_4434_);
                    leanh::lean_dec(v___x_4433_);
                    v___x_4436_ = lean_nat_dec_eq(v___x_4432_, v___x_4435_);
                    leanh::lean_dec(v___x_4435_);
                    leanh::lean_dec(v___x_4432_);
                    if v___x_4436_ == 0 {
                        leanh::lean_dec(v___x_4430_);
                        leanh::lean_dec(v_a_4428_);
                        leanh::lean_dec_ref(v___y_4420_);
                        leanh::lean_dec(v___y_4419_);
                        leanh::lean_dec(v___y_4417_);
                        leanh::lean_dec_ref(v___y_4415_);
                        leanh::lean_dec(v___y_4414_);
                        leanh::lean_dec(v___y_4413_);
                        leanh::lean_dec(v___y_4412_);
                        leanh::lean_dec_ref(v_ctors_4204_);
                        leanh::lean_dec(v_indName_4203_);
                        v___x_4437_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkSparseCasesOn___closed__4),
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkSparseCasesOn___closed__4_once),
                            _init_l_Lean_Meta_mkSparseCasesOn___closed__4,
                        );
                        v___x_4438_ = l_Lean_MessageData_ofConstName(v___x_4425_, v___x_4436_);
                        v___x_4439_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4439_, 0, v___x_4437_);
                        leanh::lean_ctor_set(v___x_4439_, 1, v___x_4438_);
                        v___x_4440_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1);
                        v___x_4441_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4441_, 0, v___x_4439_);
                        leanh::lean_ctor_set(v___x_4441_, 1, v___x_4440_);
                        v___x_4442_ =
                            l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(
                                v___x_4441_,
                                v___y_4421_,
                                v___y_4422_,
                                v___y_4423_,
                                v___y_4424_,
                            );
                        v_a_4443_ = leanh::lean_ctor_get(v___x_4442_, 0);
                        v_isSharedCheck_4450_ =
                            (!leanh::lean_is_exclusive(v___x_4442_)) as u8;
                        if v_isSharedCheck_4450_ == 0 {
                            v___x_4445_ = v___x_4442_;
                            v_isShared_4446_ = v_isSharedCheck_4450_;
                            state = 27;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4443_);
                            leanh::lean_dec(v___x_4442_);
                            v___x_4445_ = leanh::lean_box(0);
                            v_isShared_4446_ = v_isSharedCheck_4450_;
                            state = 27;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_a_4428_);
                        v___y_4216_ = v_a_4428_;
                        v___y_4217_ = v___y_4412_;
                        v___y_4218_ = v___y_4413_;
                        v___y_4219_ = v___y_4414_;
                        v___y_4220_ = v___x_4425_;
                        v___y_4221_ = v___x_4430_;
                        v___y_4222_ = v___y_4416_;
                        v___y_4223_ = v_a_4428_;
                        v___y_4224_ = v___y_4417_;
                        v___y_4225_ = v___y_4418_;
                        v___y_4226_ = v___y_4419_;
                        v___y_4227_ = v___y_4415_;
                        v___y_4228_ = v___y_4420_;
                        v___y_4229_ = v___y_4421_;
                        v___y_4230_ = v___y_4422_;
                        v___y_4231_ = v___y_4423_;
                        v___y_4232_ = v___y_4424_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_4425_);
                    leanh::lean_dec_ref(v___y_4420_);
                    leanh::lean_dec(v___y_4419_);
                    leanh::lean_dec(v___y_4417_);
                    leanh::lean_dec_ref(v___y_4415_);
                    leanh::lean_dec(v___y_4414_);
                    leanh::lean_dec(v___y_4413_);
                    leanh::lean_dec(v___y_4412_);
                    leanh::lean_dec_ref(v_ctors_4204_);
                    leanh::lean_dec(v_indName_4203_);
                    v_a_4451_ = leanh::lean_ctor_get(v___x_4426_, 0);
                    v_isSharedCheck_4458_ = (!leanh::lean_is_exclusive(v___x_4426_)) as u8;
                    if v_isSharedCheck_4458_ == 0 {
                        v___x_4453_ = v___x_4426_;
                        v_isShared_4454_ = v_isSharedCheck_4458_;
                        state = 29;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4451_);
                        leanh::lean_dec(v___x_4426_);
                        v___x_4453_ = leanh::lean_box(0);
                        v_isShared_4454_ = v_isSharedCheck_4458_;
                        state = 29;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_4446_ == 0 {
                    v___x_4448_ = v___x_4445_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4449_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_a_4443_);
                    v___x_4448_ = v_reuseFailAlloc_4449_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4448_;
            }
            29 => {
                if v_isShared_4454_ == 0 {
                    v___x_4456_ = v___x_4453_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4457_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
                    v___x_4456_ = v_reuseFailAlloc_4457_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_4456_;
            }
            31 => {
                v___x_4462_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt;
                v_asyncMode_4463_ = leanh::lean_ctor_get(v___x_4462_, 2);
                leanh::lean_inc_ref(v_ctors_4204_);
                leanh::lean_inc(v_indName_4203_);
                v___x_4464_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_4464_, 0, v_indName_4203_);
                leanh::lean_ctor_set(v___x_4464_, 1, v_ctors_4204_);
                leanh::lean_ctor_set_uint8(
                    v___x_4464_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___y_4461_,
                );
                v___x_4465_ = leanh::lean_box(0);
                v___x_4466_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_4459_,
                        v___x_4462_,
                        v_env_4211_,
                        v_asyncMode_4463_,
                        v___x_4465_,
                    );
                v___x_4467_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v___x_4466_, v___x_4464_);
                leanh::lean_dec(v___x_4466_);
                if leanh::lean_obj_tag(v___x_4467_) == 1 {
                    leanh::lean_dec_ref_known(v___x_4464_, 2);
                    leanh::lean_dec_ref(v_ctors_4204_);
                    leanh::lean_dec(v_indName_4203_);
                    v_val_4468_ = leanh::lean_ctor_get(v___x_4467_, 0);
                    v_isSharedCheck_4475_ = (!leanh::lean_is_exclusive(v___x_4467_)) as u8;
                    if v_isSharedCheck_4475_ == 0 {
                        v___x_4470_ = v___x_4467_;
                        v_isShared_4471_ = v_isSharedCheck_4475_;
                        state = 32;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4468_);
                        leanh::lean_dec(v___x_4467_);
                        v___x_4470_ = leanh::lean_box(0);
                        v_isShared_4471_ = v_isSharedCheck_4475_;
                        state = 32;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_4467_);
                    v___x_4476_ = l_Lean_Meta_mkSparseCasesOn___closed__7;
                    v___x_4477_ =
                        l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(
                            v___x_4476_,
                            v_a_4208_,
                        );
                    v_a_4478_ = leanh::lean_ctor_get(v___x_4477_, 0);
                    leanh::lean_inc(v_a_4478_);
                    leanh::lean_dec_ref(v___x_4477_);
                    leanh::lean_inc(v_indName_4203_);
                    v___x_4479_ =
                        l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__4(
                            v_indName_4203_,
                            v_a_4205_,
                            v_a_4206_,
                            v_a_4207_,
                            v_a_4208_,
                        );
                    if leanh::lean_obj_tag(v___x_4479_) == 0 {
                        v_a_4480_ = leanh::lean_ctor_get(v___x_4479_, 0);
                        leanh::lean_inc(v_a_4480_);
                        leanh::lean_dec_ref_known(v___x_4479_, 1);
                        v___x_4481_ = leanh::lean_box(0);
                        v_sz_4482_ = lean_array_size(v_ctors_4204_);
                        v___x_4483_ = 0usize;
                        leanh::lean_inc(v_indName_4203_);
                        v___x_4484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__18(v_a_4480_, v_indName_4203_, v_ctors_4204_, v_sz_4482_, v___x_4483_, v___x_4481_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_);
                        if leanh::lean_obj_tag(v___x_4484_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4484_, 1);
                            v_numParams_4485_ = leanh::lean_ctor_get(v_a_4480_, 1);
                            leanh::lean_inc(v_numParams_4485_);
                            v_numIndices_4486_ = leanh::lean_ctor_get(v_a_4480_, 2);
                            leanh::lean_inc(v_numIndices_4486_);
                            v_ctors_4487_ = leanh::lean_ctor_get(v_a_4480_, 4);
                            leanh::lean_inc(v_ctors_4487_);
                            leanh::lean_inc(v_a_4478_);
                            v___f_4488_ = leanh::lean_alloc_closure(
                                l_Lean_Meta_mkSparseCasesOn___lam__0 as *mut core::ffi::c_void,
                                3,
                                2,
                            );
                            leanh::lean_closure_set(v___f_4488_, 0, v___x_4464_);
                            leanh::lean_closure_set(v___f_4488_, 1, v_a_4478_);
                            v___x_4489_ = lean_array_get_size(v_ctors_4204_);
                            v___x_4490_ = l_List_lengthTR___redArg(v_ctors_4487_);
                            v___x_4491_ = lean_nat_dec_eq(v___x_4489_, v___x_4490_);
                            leanh::lean_dec(v___x_4490_);
                            if v___x_4491_ == 0 {
                                v___y_4412_ = v_numParams_4485_;
                                v___y_4413_ = v_ctors_4487_;
                                v___y_4414_ = v_numIndices_4486_;
                                v___y_4415_ = v___f_4488_;
                                v___y_4416_ = v_asyncMode_4463_;
                                v___y_4417_ = v_a_4478_;
                                v___y_4418_ = v___x_4462_;
                                v___y_4419_ = v___x_4465_;
                                v___y_4420_ = v_a_4480_;
                                v___y_4421_ = v_a_4205_;
                                v___y_4422_ = v_a_4206_;
                                v___y_4423_ = v_a_4207_;
                                v___y_4424_ = v_a_4208_;
                                state = 26;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v___f_4488_);
                                leanh::lean_dec(v_ctors_4487_);
                                leanh::lean_dec(v_numIndices_4486_);
                                leanh::lean_dec(v_numParams_4485_);
                                leanh::lean_dec(v_a_4480_);
                                leanh::lean_dec(v_a_4478_);
                                leanh::lean_dec_ref(v_ctors_4204_);
                                leanh::lean_dec(v_indName_4203_);
                                v___x_4492_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_mkSparseCasesOn___closed__9
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_mkSparseCasesOn___closed__9_once
                                    ),
                                    _init_l_Lean_Meta_mkSparseCasesOn___closed__9,
                                );
                                v___x_4493_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(v___x_4492_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_);
                                v_a_4494_ = leanh::lean_ctor_get(v___x_4493_, 0);
                                v_isSharedCheck_4501_ =
                                    (!leanh::lean_is_exclusive(v___x_4493_)) as u8;
                                if v_isSharedCheck_4501_ == 0 {
                                    v___x_4496_ = v___x_4493_;
                                    v_isShared_4497_ = v_isSharedCheck_4501_;
                                    state = 34;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4494_);
                                    leanh::lean_dec(v___x_4493_);
                                    v___x_4496_ = leanh::lean_box(0);
                                    v_isShared_4497_ = v_isSharedCheck_4501_;
                                    state = 34;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_4480_);
                            leanh::lean_dec(v_a_4478_);
                            leanh::lean_dec_ref_known(v___x_4464_, 2);
                            leanh::lean_dec_ref(v_ctors_4204_);
                            leanh::lean_dec(v_indName_4203_);
                            v_a_4502_ = leanh::lean_ctor_get(v___x_4484_, 0);
                            v_isSharedCheck_4509_ =
                                (!leanh::lean_is_exclusive(v___x_4484_)) as u8;
                            if v_isSharedCheck_4509_ == 0 {
                                v___x_4504_ = v___x_4484_;
                                v_isShared_4505_ = v_isSharedCheck_4509_;
                                state = 36;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4502_);
                                leanh::lean_dec(v___x_4484_);
                                v___x_4504_ = leanh::lean_box(0);
                                v_isShared_4505_ = v_isSharedCheck_4509_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_4478_);
                        leanh::lean_dec_ref_known(v___x_4464_, 2);
                        leanh::lean_dec_ref(v_ctors_4204_);
                        leanh::lean_dec(v_indName_4203_);
                        v_a_4510_ = leanh::lean_ctor_get(v___x_4479_, 0);
                        v_isSharedCheck_4517_ =
                            (!leanh::lean_is_exclusive(v___x_4479_)) as u8;
                        if v_isSharedCheck_4517_ == 0 {
                            v___x_4512_ = v___x_4479_;
                            v_isShared_4513_ = v_isSharedCheck_4517_;
                            state = 38;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4510_);
                            leanh::lean_dec(v___x_4479_);
                            v___x_4512_ = leanh::lean_box(0);
                            v_isShared_4513_ = v_isSharedCheck_4517_;
                            state = 38;
                            continue;
                        }
                    }
                }
            }
            32 => {
                if v_isShared_4471_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4470_, 0);
                    v___x_4473_ = v___x_4470_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4474_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_val_4468_);
                    v___x_4473_ = v_reuseFailAlloc_4474_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_4473_;
            }
            34 => {
                if v_isShared_4497_ == 0 {
                    v___x_4499_ = v___x_4496_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_4500_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4494_);
                    v___x_4499_ = v_reuseFailAlloc_4500_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_4499_;
            }
            36 => {
                if v_isShared_4505_ == 0 {
                    v___x_4507_ = v___x_4504_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4508_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4502_);
                    v___x_4507_ = v_reuseFailAlloc_4508_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_4507_;
            }
            38 => {
                if v_isShared_4513_ == 0 {
                    v___x_4515_ = v___x_4512_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_4516_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4516_, 0, v_a_4510_);
                    v___x_4515_ = v_reuseFailAlloc_4516_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_4515_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkSparseCasesOn___boxed(
    mut v_indName_4520_: *mut leanh::LeanObject,
    mut v_ctors_4521_: *mut leanh::LeanObject,
    mut v_a_4522_: *mut leanh::LeanObject,
    mut v_a_4523_: *mut leanh::LeanObject,
    mut v_a_4524_: *mut leanh::LeanObject,
    mut v_a_4525_: *mut leanh::LeanObject,
    mut v_a_4526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4527_ = l_Lean_Meta_mkSparseCasesOn(
        v_indName_4520_,
        v_ctors_4521_,
        v_a_4522_,
        v_a_4523_,
        v_a_4524_,
        v_a_4525_,
    );
    leanh::lean_dec(v_a_4525_);
    leanh::lean_dec_ref(v_a_4524_);
    leanh::lean_dec(v_a_4523_);
    leanh::lean_dec_ref(v_a_4522_);
    return v_res_4527_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(
    mut v_00_u03b2_4528_: *mut leanh::LeanObject,
    mut v_x_4529_: *mut leanh::LeanObject,
    mut v_x_4530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4531_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(
            v_x_4529_, v_x_4530_,
        );
    return v___x_4531_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___boxed(
    mut v_00_u03b2_4532_: *mut leanh::LeanObject,
    mut v_x_4533_: *mut leanh::LeanObject,
    mut v_x_4534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4535_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(
        v_00_u03b2_4532_,
        v_x_4533_,
        v_x_4534_,
    );
    leanh::lean_dec_ref(v_x_4534_);
    leanh::lean_dec_ref(v_x_4533_);
    return v_res_4535_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3(
    mut v_00_u03b2_4536_: *mut leanh::LeanObject,
    mut v_x_4537_: *mut leanh::LeanObject,
    mut v_x_4538_: *mut leanh::LeanObject,
    mut v_x_4539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4540_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(
            v_x_4537_, v_x_4538_, v_x_4539_,
        );
    return v___x_4540_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13(
    mut v_00_u03b1_4541_: *mut leanh::LeanObject,
    mut v_name_4542_: *mut leanh::LeanObject,
    mut v_bi_4543_: u8,
    mut v_type_4544_: *mut leanh::LeanObject,
    mut v_k_4545_: *mut leanh::LeanObject,
    mut v_kind_4546_: u8,
    mut v___y_4547_: *mut leanh::LeanObject,
    mut v___y_4548_: *mut leanh::LeanObject,
    mut v___y_4549_: *mut leanh::LeanObject,
    mut v___y_4550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4552_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___redArg(v_name_4542_, v_bi_4543_, v_type_4544_, v_k_4545_, v_kind_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_);
    return v___x_4552_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13___boxed(
    mut v_00_u03b1_4553_: *mut leanh::LeanObject,
    mut v_name_4554_: *mut leanh::LeanObject,
    mut v_bi_4555_: *mut leanh::LeanObject,
    mut v_type_4556_: *mut leanh::LeanObject,
    mut v_k_4557_: *mut leanh::LeanObject,
    mut v_kind_4558_: *mut leanh::LeanObject,
    mut v___y_4559_: *mut leanh::LeanObject,
    mut v___y_4560_: *mut leanh::LeanObject,
    mut v___y_4561_: *mut leanh::LeanObject,
    mut v___y_4562_: *mut leanh::LeanObject,
    mut v___y_4563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_4564_: u8 = 0;
    let mut v_kind_boxed_4565_: u8 = 0;
    let mut v_res_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4564_ = (leanh::lean_unbox(v_bi_4555_) as u8);
    v_kind_boxed_4565_ = (leanh::lean_unbox(v_kind_4558_) as u8);
    v_res_4566_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9_spec__13(v_00_u03b1_4553_, v_name_4554_, v_bi_boxed_4564_, v_type_4556_, v_k_4557_, v_kind_boxed_4565_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
    leanh::lean_dec(v___y_4562_);
    leanh::lean_dec_ref(v___y_4561_);
    leanh::lean_dec(v___y_4560_);
    leanh::lean_dec_ref(v___y_4559_);
    return v_res_4566_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9(
    mut v_00_u03b1_4567_: *mut leanh::LeanObject,
    mut v_name_4568_: *mut leanh::LeanObject,
    mut v_type_4569_: *mut leanh::LeanObject,
    mut v_k_4570_: *mut leanh::LeanObject,
    mut v___y_4571_: *mut leanh::LeanObject,
    mut v___y_4572_: *mut leanh::LeanObject,
    mut v___y_4573_: *mut leanh::LeanObject,
    mut v___y_4574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4576_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___redArg(
        v_name_4568_,
        v_type_4569_,
        v_k_4570_,
        v___y_4571_,
        v___y_4572_,
        v___y_4573_,
        v___y_4574_,
    );
    return v___x_4576_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9___boxed(
    mut v_00_u03b1_4577_: *mut leanh::LeanObject,
    mut v_name_4578_: *mut leanh::LeanObject,
    mut v_type_4579_: *mut leanh::LeanObject,
    mut v_k_4580_: *mut leanh::LeanObject,
    mut v___y_4581_: *mut leanh::LeanObject,
    mut v___y_4582_: *mut leanh::LeanObject,
    mut v___y_4583_: *mut leanh::LeanObject,
    mut v___y_4584_: *mut leanh::LeanObject,
    mut v___y_4585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4586_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__9(
        v_00_u03b1_4577_,
        v_name_4578_,
        v_type_4579_,
        v_k_4580_,
        v___y_4581_,
        v___y_4582_,
        v___y_4583_,
        v___y_4584_,
    );
    leanh::lean_dec(v___y_4584_);
    leanh::lean_dec_ref(v___y_4583_);
    leanh::lean_dec(v___y_4582_);
    leanh::lean_dec_ref(v___y_4581_);
    return v_res_4586_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13(
    mut v_00_u03b1_4587_: *mut leanh::LeanObject,
    mut v_msg_4588_: *mut leanh::LeanObject,
    mut v___y_4589_: *mut leanh::LeanObject,
    mut v___y_4590_: *mut leanh::LeanObject,
    mut v___y_4591_: *mut leanh::LeanObject,
    mut v___y_4592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4594_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___redArg(
        v_msg_4588_,
        v___y_4589_,
        v___y_4590_,
        v___y_4591_,
        v___y_4592_,
    );
    return v___x_4594_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13___boxed(
    mut v_00_u03b1_4595_: *mut leanh::LeanObject,
    mut v_msg_4596_: *mut leanh::LeanObject,
    mut v___y_4597_: *mut leanh::LeanObject,
    mut v___y_4598_: *mut leanh::LeanObject,
    mut v___y_4599_: *mut leanh::LeanObject,
    mut v___y_4600_: *mut leanh::LeanObject,
    mut v___y_4601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4602_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__13(
        v_00_u03b1_4595_,
        v_msg_4596_,
        v___y_4597_,
        v___y_4598_,
        v___y_4599_,
        v___y_4600_,
    );
    leanh::lean_dec(v___y_4600_);
    leanh::lean_dec_ref(v___y_4599_);
    leanh::lean_dec(v___y_4598_);
    leanh::lean_dec_ref(v___y_4597_);
    return v_res_4602_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22(
    mut v_declName_4603_: *mut leanh::LeanObject,
    mut v_s_4604_: u8,
    mut v___y_4605_: *mut leanh::LeanObject,
    mut v___y_4606_: *mut leanh::LeanObject,
    mut v___y_4607_: *mut leanh::LeanObject,
    mut v___y_4608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4610_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___redArg(v_declName_4603_, v_s_4604_, v___y_4606_, v___y_4608_);
    return v___x_4610_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22___boxed(
    mut v_declName_4611_: *mut leanh::LeanObject,
    mut v_s_4612_: *mut leanh::LeanObject,
    mut v___y_4613_: *mut leanh::LeanObject,
    mut v___y_4614_: *mut leanh::LeanObject,
    mut v___y_4615_: *mut leanh::LeanObject,
    mut v___y_4616_: *mut leanh::LeanObject,
    mut v___y_4617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_boxed_4618_: u8 = 0;
    let mut v_res_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_4618_ = (leanh::lean_unbox(v_s_4612_) as u8);
    v_res_4619_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__15_spec__22(v_declName_4611_, v_s_boxed_4618_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
    leanh::lean_dec(v___y_4616_);
    leanh::lean_dec_ref(v___y_4615_);
    leanh::lean_dec(v___y_4614_);
    leanh::lean_dec_ref(v___y_4613_);
    return v_res_4619_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(
    mut v_00_u03b2_4620_: *mut leanh::LeanObject,
    mut v_x_4621_: *mut leanh::LeanObject,
    mut v_x_4622_: usize,
    mut v_x_4623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4624_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_4621_, v_x_4622_, v_x_4623_);
    return v___x_4624_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___boxed(
    mut v_00_u03b2_4625_: *mut leanh::LeanObject,
    mut v_x_4626_: *mut leanh::LeanObject,
    mut v_x_4627_: *mut leanh::LeanObject,
    mut v_x_4628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_23967__boxed_4629_: usize = 0;
    let mut v_res_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_23967__boxed_4629_ = leanh::lean_unbox_usize(v_x_4627_);
    leanh::lean_dec(v_x_4627_);
    v_res_4630_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(v_00_u03b2_4625_, v_x_4626_, v_x_23967__boxed_4629_, v_x_4628_);
    leanh::lean_dec_ref(v_x_4628_);
    leanh::lean_dec_ref(v_x_4626_);
    return v_res_4630_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(
    mut v_00_u03b2_4631_: *mut leanh::LeanObject,
    mut v_x_4632_: *mut leanh::LeanObject,
    mut v_x_4633_: usize,
    mut v_x_4634_: usize,
    mut v_x_4635_: *mut leanh::LeanObject,
    mut v_x_4636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4637_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_4632_, v_x_4633_, v_x_4634_, v_x_4635_, v_x_4636_);
    return v___x_4637_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___boxed(
    mut v_00_u03b2_4638_: *mut leanh::LeanObject,
    mut v_x_4639_: *mut leanh::LeanObject,
    mut v_x_4640_: *mut leanh::LeanObject,
    mut v_x_4641_: *mut leanh::LeanObject,
    mut v_x_4642_: *mut leanh::LeanObject,
    mut v_x_4643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_23978__boxed_4644_: usize = 0;
    let mut v_x_23979__boxed_4645_: usize = 0;
    let mut v_res_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_23978__boxed_4644_ = leanh::lean_unbox_usize(v_x_4640_);
    leanh::lean_dec(v_x_4640_);
    v_x_23979__boxed_4645_ = leanh::lean_unbox_usize(v_x_4641_);
    leanh::lean_dec(v_x_4641_);
    v_res_4646_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(v_00_u03b2_4638_, v_x_4639_, v_x_23978__boxed_4644_, v_x_23979__boxed_4645_, v_x_4642_, v_x_4643_);
    return v_res_4646_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8(
    mut v_00_u03b1_4647_: *mut leanh::LeanObject,
    mut v_constName_4648_: *mut leanh::LeanObject,
    mut v___y_4649_: *mut leanh::LeanObject,
    mut v___y_4650_: *mut leanh::LeanObject,
    mut v___y_4651_: *mut leanh::LeanObject,
    mut v___y_4652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4654_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___redArg(v_constName_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_);
    return v___x_4654_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8___boxed(
    mut v_00_u03b1_4655_: *mut leanh::LeanObject,
    mut v_constName_4656_: *mut leanh::LeanObject,
    mut v___y_4657_: *mut leanh::LeanObject,
    mut v___y_4658_: *mut leanh::LeanObject,
    mut v___y_4659_: *mut leanh::LeanObject,
    mut v___y_4660_: *mut leanh::LeanObject,
    mut v___y_4661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4662_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8(v_00_u03b1_4655_, v_constName_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
    leanh::lean_dec(v___y_4660_);
    leanh::lean_dec_ref(v___y_4659_);
    leanh::lean_dec(v___y_4658_);
    leanh::lean_dec_ref(v___y_4657_);
    return v_res_4662_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7(
    mut v_00_u03b2_4663_: *mut leanh::LeanObject,
    mut v_keys_4664_: *mut leanh::LeanObject,
    mut v_vals_4665_: *mut leanh::LeanObject,
    mut v_heq_4666_: *mut leanh::LeanObject,
    mut v_i_4667_: *mut leanh::LeanObject,
    mut v_k_4668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4669_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___redArg(v_keys_4664_, v_vals_4665_, v_i_4667_, v_k_4668_);
    return v___x_4669_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7___boxed(
    mut v_00_u03b2_4670_: *mut leanh::LeanObject,
    mut v_keys_4671_: *mut leanh::LeanObject,
    mut v_vals_4672_: *mut leanh::LeanObject,
    mut v_heq_4673_: *mut leanh::LeanObject,
    mut v_i_4674_: *mut leanh::LeanObject,
    mut v_k_4675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4676_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__7(v_00_u03b2_4670_, v_keys_4671_, v_vals_4672_, v_heq_4673_, v_i_4674_, v_k_4675_);
    leanh::lean_dec_ref(v_k_4675_);
    leanh::lean_dec_ref(v_vals_4672_);
    leanh::lean_dec_ref(v_keys_4671_);
    return v_res_4676_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10(
    mut v_00_u03b2_4677_: *mut leanh::LeanObject,
    mut v_n_4678_: *mut leanh::LeanObject,
    mut v_k_4679_: *mut leanh::LeanObject,
    mut v_v_4680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4681_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10___redArg(v_n_4678_, v_k_4679_, v_v_4680_);
    return v___x_4681_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11(
    mut v_00_u03b2_4682_: *mut leanh::LeanObject,
    mut v_depth_4683_: usize,
    mut v_keys_4684_: *mut leanh::LeanObject,
    mut v_vals_4685_: *mut leanh::LeanObject,
    mut v_heq_4686_: *mut leanh::LeanObject,
    mut v_i_4687_: *mut leanh::LeanObject,
    mut v_entries_4688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4689_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(v_depth_4683_, v_keys_4684_, v_vals_4685_, v_i_4687_, v_entries_4688_);
    return v___x_4689_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___boxed(
    mut v_00_u03b2_4690_: *mut leanh::LeanObject,
    mut v_depth_4691_: *mut leanh::LeanObject,
    mut v_keys_4692_: *mut leanh::LeanObject,
    mut v_vals_4693_: *mut leanh::LeanObject,
    mut v_heq_4694_: *mut leanh::LeanObject,
    mut v_i_4695_: *mut leanh::LeanObject,
    mut v_entries_4696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4697_: usize = 0;
    let mut v_res_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4697_ = leanh::lean_unbox_usize(v_depth_4691_);
    leanh::lean_dec(v_depth_4691_);
    v_res_4698_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11(v_00_u03b2_4690_, v_depth_boxed_4697_, v_keys_4692_, v_vals_4693_, v_heq_4694_, v_i_4695_, v_entries_4696_);
    leanh::lean_dec_ref(v_vals_4693_);
    leanh::lean_dec_ref(v_keys_4692_);
    return v_res_4698_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15(
    mut v_00_u03b1_4699_: *mut leanh::LeanObject,
    mut v_ref_4700_: *mut leanh::LeanObject,
    mut v_constName_4701_: *mut leanh::LeanObject,
    mut v___y_4702_: *mut leanh::LeanObject,
    mut v___y_4703_: *mut leanh::LeanObject,
    mut v___y_4704_: *mut leanh::LeanObject,
    mut v___y_4705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4707_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___redArg(v_ref_4700_, v_constName_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_);
    return v___x_4707_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15___boxed(
    mut v_00_u03b1_4708_: *mut leanh::LeanObject,
    mut v_ref_4709_: *mut leanh::LeanObject,
    mut v_constName_4710_: *mut leanh::LeanObject,
    mut v___y_4711_: *mut leanh::LeanObject,
    mut v___y_4712_: *mut leanh::LeanObject,
    mut v___y_4713_: *mut leanh::LeanObject,
    mut v___y_4714_: *mut leanh::LeanObject,
    mut v___y_4715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4716_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15(v_00_u03b1_4708_, v_ref_4709_, v_constName_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_);
    leanh::lean_dec(v___y_4714_);
    leanh::lean_dec_ref(v___y_4713_);
    leanh::lean_dec(v___y_4712_);
    leanh::lean_dec_ref(v___y_4711_);
    leanh::lean_dec(v_ref_4709_);
    return v_res_4716_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26(
    mut v_00_u03b2_4717_: *mut leanh::LeanObject,
    mut v_x_4718_: *mut leanh::LeanObject,
    mut v_x_4719_: *mut leanh::LeanObject,
    mut v_x_4720_: *mut leanh::LeanObject,
    mut v_x_4721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4722_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__10_spec__26___redArg(v_x_4718_, v_x_4719_, v_x_4720_, v_x_4721_);
    return v___x_4722_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30(
    mut v_00_u03b1_4723_: *mut leanh::LeanObject,
    mut v_ref_4724_: *mut leanh::LeanObject,
    mut v_msg_4725_: *mut leanh::LeanObject,
    mut v_declHint_4726_: *mut leanh::LeanObject,
    mut v___y_4727_: *mut leanh::LeanObject,
    mut v___y_4728_: *mut leanh::LeanObject,
    mut v___y_4729_: *mut leanh::LeanObject,
    mut v___y_4730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4732_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___redArg(v_ref_4724_, v_msg_4725_, v_declHint_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_);
    return v___x_4732_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30___boxed(
    mut v_00_u03b1_4733_: *mut leanh::LeanObject,
    mut v_ref_4734_: *mut leanh::LeanObject,
    mut v_msg_4735_: *mut leanh::LeanObject,
    mut v_declHint_4736_: *mut leanh::LeanObject,
    mut v___y_4737_: *mut leanh::LeanObject,
    mut v___y_4738_: *mut leanh::LeanObject,
    mut v___y_4739_: *mut leanh::LeanObject,
    mut v___y_4740_: *mut leanh::LeanObject,
    mut v___y_4741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4742_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30(v_00_u03b1_4733_, v_ref_4734_, v_msg_4735_, v_declHint_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_);
    leanh::lean_dec(v___y_4740_);
    leanh::lean_dec_ref(v___y_4739_);
    leanh::lean_dec(v___y_4738_);
    leanh::lean_dec_ref(v___y_4737_);
    leanh::lean_dec(v_ref_4734_);
    return v_res_4742_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34(
    mut v_msg_4743_: *mut leanh::LeanObject,
    mut v_declHint_4744_: *mut leanh::LeanObject,
    mut v___y_4745_: *mut leanh::LeanObject,
    mut v___y_4746_: *mut leanh::LeanObject,
    mut v___y_4747_: *mut leanh::LeanObject,
    mut v___y_4748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4750_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___redArg(v_msg_4743_, v_declHint_4744_, v___y_4748_);
    return v___x_4750_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34___boxed(
    mut v_msg_4751_: *mut leanh::LeanObject,
    mut v_declHint_4752_: *mut leanh::LeanObject,
    mut v___y_4753_: *mut leanh::LeanObject,
    mut v___y_4754_: *mut leanh::LeanObject,
    mut v___y_4755_: *mut leanh::LeanObject,
    mut v___y_4756_: *mut leanh::LeanObject,
    mut v___y_4757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4758_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__32_spec__34(v_msg_4751_, v_declHint_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_);
    leanh::lean_dec(v___y_4756_);
    leanh::lean_dec_ref(v___y_4755_);
    leanh::lean_dec(v___y_4754_);
    leanh::lean_dec_ref(v___y_4753_);
    return v_res_4758_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33(
    mut v_00_u03b1_4759_: *mut leanh::LeanObject,
    mut v_ref_4760_: *mut leanh::LeanObject,
    mut v_msg_4761_: *mut leanh::LeanObject,
    mut v___y_4762_: *mut leanh::LeanObject,
    mut v___y_4763_: *mut leanh::LeanObject,
    mut v___y_4764_: *mut leanh::LeanObject,
    mut v___y_4765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4767_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___redArg(v_ref_4760_, v_msg_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
    return v___x_4767_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33___boxed(
    mut v_00_u03b1_4768_: *mut leanh::LeanObject,
    mut v_ref_4769_: *mut leanh::LeanObject,
    mut v_msg_4770_: *mut leanh::LeanObject,
    mut v___y_4771_: *mut leanh::LeanObject,
    mut v___y_4772_: *mut leanh::LeanObject,
    mut v___y_4773_: *mut leanh::LeanObject,
    mut v___y_4774_: *mut leanh::LeanObject,
    mut v___y_4775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4776_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__5_spec__8_spec__15_spec__30_spec__33(v_00_u03b1_4768_, v_ref_4769_, v_msg_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_);
    leanh::lean_dec(v___y_4774_);
    leanh::lean_dec_ref(v___y_4773_);
    leanh::lean_dec(v___y_4772_);
    leanh::lean_dec_ref(v___y_4771_);
    leanh::lean_dec(v_ref_4769_);
    return v_res_4776_;
}
pub unsafe fn l_Lean_Meta_getSparseCasesOnInfoCore(
    mut v_env_4777_: *mut leanh::LeanObject,
    mut v_sparseCasesOnName_4778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: u8 = 0;
    let mut v___x_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4779_ =
        l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
    v_toEnvExtension_4780_ = leanh::lean_ctor_get(v___x_4779_, 0);
    v_asyncMode_4781_ = leanh::lean_ctor_get(v_toEnvExtension_4780_, 2);
    v___x_4782_ = l_Lean_Meta_instInhabitedSparseCasesOnInfo_default;
    v___x_4783_ = 0;
    v___x_4784_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
        v___x_4782_,
        v___x_4779_,
        v_env_4777_,
        v_sparseCasesOnName_4778_,
        v_asyncMode_4781_,
        v___x_4783_,
    );
    return v___x_4784_;
}
pub unsafe fn l_Lean_Meta_getSparseCasesOnInfo___redArg(
    mut v_sparseCasesOnName_4785_: *mut leanh::LeanObject,
    mut v_a_4786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: u8 = 0;
    let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4788_ = lean_st_ref_get(v_a_4786_);
    v_env_4789_ = leanh::lean_ctor_get(v___x_4788_, 0);
    leanh::lean_inc_ref(v_env_4789_);
    leanh::lean_dec(v___x_4788_);
    v___x_4790_ =
        l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
    v_toEnvExtension_4791_ = leanh::lean_ctor_get(v___x_4790_, 0);
    v_asyncMode_4792_ = leanh::lean_ctor_get(v_toEnvExtension_4791_, 2);
    v___x_4793_ = l_Lean_Meta_instInhabitedSparseCasesOnInfo_default;
    v___x_4794_ = 0;
    v___x_4795_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
        v___x_4793_,
        v___x_4790_,
        v_env_4789_,
        v_sparseCasesOnName_4785_,
        v_asyncMode_4792_,
        v___x_4794_,
    );
    v___x_4796_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4796_, 0, v___x_4795_);
    return v___x_4796_;
}
pub unsafe fn l_Lean_Meta_getSparseCasesOnInfo___redArg___boxed(
    mut v_sparseCasesOnName_4797_: *mut leanh::LeanObject,
    mut v_a_4798_: *mut leanh::LeanObject,
    mut v_a_4799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4800_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_4797_, v_a_4798_);
    leanh::lean_dec(v_a_4798_);
    return v_res_4800_;
}
pub unsafe fn l_Lean_Meta_getSparseCasesOnInfo(
    mut v_sparseCasesOnName_4801_: *mut leanh::LeanObject,
    mut v_a_4802_: *mut leanh::LeanObject,
    mut v_a_4803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4805_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_4801_, v_a_4803_);
    return v___x_4805_;
}
pub unsafe fn l_Lean_Meta_getSparseCasesOnInfo___boxed(
    mut v_sparseCasesOnName_4806_: *mut leanh::LeanObject,
    mut v_a_4807_: *mut leanh::LeanObject,
    mut v_a_4808_: *mut leanh::LeanObject,
    mut v_a_4809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4810_ = l_Lean_Meta_getSparseCasesOnInfo(v_sparseCasesOnName_4806_, v_a_4807_, v_a_4808_);
    leanh::lean_dec(v_a_4808_);
    leanh::lean_dec_ref(v_a_4807_);
    return v_res_4810_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(
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
    res = runtime_initialize_Lean_AddDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_HasNotBit(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Transform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1993625133____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt =
        leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(
        l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt,
    );
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_869743855____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt =
        leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(
        l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt,
    );
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Constructions_SparseCasesOn(
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
pub unsafe fn initialize_Lean_Meta_Constructions_SparseCasesOn(
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
    res = initialize_Lean_AddDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_HasNotBit(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Transform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
}
// Lean compiler output
// Module: Lean.ResolveName
// Imports: Lean.Modifiers Lean.Exception Lean.Namespace Lean.Log
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_size, lean_array_uget_borrowed,
    lean_array_uset, lean_mk_array, lean_name_eq, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_div, lean_nat_mul, lean_panic_fn_borrowed, lean_st_mk_ref, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_string_append, lean_uint64_of_nat,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land, lean_usize_mul,
    lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::Option::{
    l_OptionT_bind, l_OptionT_instAlternative___redArg, l_OptionT_instMonad___redArg___lam__1,
    l_OptionT_instMonad___redArg___lam__3, l_OptionT_instMonad___redArg___lam__6,
    l_OptionT_instMonad___redArg___lam__9, l_OptionT_instMonad___redArg___lam__11, l_OptionT_lift,
    l_OptionT_lift___redArg___lam__0, l_OptionT_pure,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_firstM_go,
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold, l_Array_instInhabited,
};
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Format::Syntax::l_Lean_Syntax_formatStx;
use crate::r#gen::Init::Data::List::Basic::{
    l_List_appendTR___redArg, l_List_eraseDupsBy___redArg, l_List_filterTR_loop___redArg,
    l_List_find_x3f___redArg, l_List_isEmpty___redArg, l_List_mapTR_loop___redArg,
    l_List_reverse___redArg,
};
use crate::r#gen::Init::Data::List::Control::l_List_forIn_x27_loop___redArg;
use crate::r#gen::Init::Data::List::Impl::l_List_filterMapTR_go___redArg;
use crate::r#gen::Init::Data::Option::Basic::l_Option_isNone___boxed;
use crate::r#gen::Init::Data::ToString::Extra::l_List_toString___redArg;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_instToString___lam__0,
    l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Meta::Defs::{l_Lean_Name_replacePrefix, l_Lean_TSyntax_getId};
use crate::r#gen::Init::Prelude::{
    l_Lean_MacroScopesView_review, l_Lean_Name_append, l_Lean_Name_appendCore,
    l_Lean_Name_beq___boxed, l_Lean_Name_hasMacroScopes, l_Lean_Name_hash___override___boxed,
    l_Lean_Name_str___override, l_Lean_extractMacroScopes, l_Lean_replaceRef,
    l_instInhabitedOfMonad___redArg, l_panic___redArg,
};
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::KVMap::l_Lean_KVMap_instValueBool;
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, l_Lean_Name_componentsRev,
    l_Lean_Name_getPrefix, l_Lean_Name_isAtomic, l_Lean_Name_isPrefixOf,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_MacroScopesView_isSuffixOf,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Data::OpenDecl::l_Lean_rootNamespace;
use crate::r#gen::Lean::Data::Options::{l_Lean_Option_getM___redArg, lean_register_option};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_findSomeRevM_x3f___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Data::SMap::l_Lean_SMap_instInhabited;
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_SimplePersistentEnvExtension_getState___redArg,
    l_Lean_registerSimplePersistentEnvExtension___redArg,
};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_Environment_contains, l_Lean_Environment_containsOnBranch,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0, l_Lean_registerEnvExtension___redArg,
};
use crate::r#gen::Lean::Exception::{
    initialize_Lean_Exception, l_Lean_throwError___redArg, l_Lean_throwErrorAt___redArg,
    l_Lean_throwUnknownConstantAt___redArg, runtime_initialize_Lean_Exception,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_dbgToString___boxed, l_Lean_mkConst};
use crate::r#gen::Lean::ImportingFlag::l_Lean_initializing;
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_isAuxDecl, l_Lean_LocalDecl_toExpr,
    l_Lean_LocalDecl_userName,
};
use crate::r#gen::Lean::Log::{
    initialize_Lean_Log, l_Lean_instMonadLogOfMonadLift___redArg, l_Lean_logWarning___redArg,
    runtime_initialize_Lean_Log,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofList, l_Lean_MessageData_ofName,
    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Modifiers::{
    initialize_Lean_Modifiers, l_Lean_isProtected, l_Lean_mkPrivateName,
    runtime_initialize_Lean_Modifiers,
};
use crate::r#gen::Lean::Namespace::{
    initialize_Lean_Namespace, l_Lean_Environment_isNamespace, runtime_initialize_Lean_Namespace,
};
use crate::r#gen::Lean::PrivateName::{
    l_Lean_isPrivateName, l_Lean_mkPrivateNameCore, l_Lean_privateToUserName,
    lean_private_to_user_name,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg;
pub static l_Lean_throwReservedNameNotAvailable___redArg___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 100, 101, 99, 108, 97, 114, 101, 32, 96, 0,
    ],
};
static mut l_Lean_throwReservedNameNotAvailable___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_throwReservedNameNotAvailable___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_throwReservedNameNotAvailable___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_throwReservedNameNotAvailable___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwReservedNameNotAvailable___redArg___closed__2_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [96, 32, 98, 101, 99, 97, 117, 115, 101, 32, 96, 0],
};
static mut l_Lean_throwReservedNameNotAvailable___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_throwReservedNameNotAvailable___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_throwReservedNameNotAvailable___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_throwReservedNameNotAvailable___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwReservedNameNotAvailable___redArg___closed__4_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        96, 32, 104, 97, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 98, 101, 101, 110, 32, 100,
        101, 99, 108, 97, 114, 101, 100, 0,
    ],
};
static mut l_Lean_throwReservedNameNotAvailable___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_throwReservedNameNotAvailable___redArg___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_throwReservedNameNotAvailable___redArg___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_throwReservedNameNotAvailable___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2__value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_reservedNamePredicatesRef: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_registerReservedNamePredicate___closed__0_value: leanh::LeanStringObject<
    110,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 110,
    m_capacity: 110,
    m_length: 109,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 103, 105, 115, 116, 101, 114, 32,
        114, 101, 115, 101, 114, 118, 101, 100, 32, 110, 97, 109, 101, 32, 115, 117, 102, 102, 105,
        120, 32, 112, 114, 101, 100, 105, 99, 97, 116, 101, 44, 32, 116, 104, 105, 115, 32, 111,
        112, 101, 114, 97, 116, 105, 111, 110, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98,
        101, 32, 112, 101, 114, 102, 111, 114, 109, 101, 100, 32, 100, 117, 114, 105, 110, 103, 32,
        105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_registerReservedNamePredicate___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerReservedNamePredicate___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_registerReservedNamePredicate___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerReservedNamePredicate___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_reservedNamePredicatesExt: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_isReservedName___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_isReservedName___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [97, 108, 105, 97, 115, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value) as *mut leanh::LeanObject,18189753109880262399 as *mut leanh::LeanObject] };
static mut l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_addAliasEntry as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value: leanh::LeanCtorObject<7> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_aliasExtension: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getAliasState___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_getAliasState___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getAliasState___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_getAliasState___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_getAliasState___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getAliasState___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_getAliasState___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getAliasState___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 99, 107, 119, 97, 114, 100, 0]};
static mut l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [112, 114, 105, 118, 97, 116, 101, 73, 110, 80, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value) as *mut leanh::LeanObject,15861075605163525197 as *mut leanh::LeanObject] };
pub static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value) as *mut leanh::LeanObject,806566856252754376 as *mut leanh::LeanObject] };
static mut l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value: leanh::LeanStringObject<227> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 227, m_capacity: 227, m_length: 226, m_data: [40, 109, 111, 100, 117, 108, 101, 32, 115, 121, 115, 116, 101, 109, 41, 32, 69, 120, 112, 111, 114, 116, 32, 96, 112, 114, 105, 118, 97, 116, 101, 96, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 44, 32, 97, 108, 108, 111, 119, 105, 110, 103, 32, 102, 111, 114, 32, 97, 114, 98, 105, 116, 114, 97, 114, 121, 32, 97, 99, 99, 101, 115, 115, 32, 116, 111, 32, 116, 104, 101, 109, 32, 119, 104, 105, 108, 101, 32, 99, 111, 100, 101, 32, 105, 115, 32, 98, 101, 105, 110, 103, 32, 112, 111, 114, 116, 101, 100, 32, 116, 111, 32, 116, 104, 101, 32, 109, 111, 100, 117, 108, 101, 32, 115, 121, 115, 116, 101, 109, 46, 32, 83, 117, 99, 104, 32, 97, 99, 99, 101, 115, 115, 101, 115, 32, 119, 105, 108, 108, 32, 103, 101, 110, 101, 114, 97, 116, 101, 32, 119, 97, 114, 110, 105, 110, 103, 115, 10, 32, 32, 32, 32, 117, 110, 108, 101, 115, 115, 32, 96, 98, 97, 99, 107, 119, 97, 114, 100, 46, 112, 114, 105, 118, 97, 116, 101, 73, 110, 80, 117, 98, 108, 105, 99, 46, 119, 97, 114, 110, 96, 32, 105, 115, 32, 100, 105, 115, 97, 98, 108, 101, 100, 46, 0]};
static mut l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [82, 101, 115, 111, 108, 118, 101, 78, 97, 109, 101, 0]};
static mut l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value) as *mut leanh::LeanObject,4665502414017888213 as *mut leanh::LeanObject] };
static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value) as *mut leanh::LeanObject,6097534712086569347 as *mut leanh::LeanObject] };
pub static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value) as *mut leanh::LeanObject,10377308656794966622 as *mut leanh::LeanObject] };
static mut l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_ResolveName_backward_privateInPublic: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [119, 97, 114, 110, 0]};
static mut l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value) as *mut leanh::LeanObject,15861075605163525197 as *mut leanh::LeanObject] };
static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value) as *mut leanh::LeanObject,806566856252754376 as *mut leanh::LeanObject] };
pub static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value) as *mut leanh::LeanObject,12221674141073552428 as *mut leanh::LeanObject] };
static mut l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value: leanh::LeanStringObject<126> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 126, m_capacity: 126, m_length: 125, m_data: [40, 109, 111, 100, 117, 108, 101, 32, 115, 121, 115, 116, 101, 109, 41, 32, 87, 97, 114, 110, 32, 111, 110, 32, 97, 99, 99, 101, 115, 115, 101, 115, 32, 116, 111, 32, 96, 112, 114, 105, 118, 97, 116, 101, 96, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 116, 104, 97, 116, 32, 97, 114, 101, 32, 97, 108, 108, 111, 119, 101, 100, 32, 111, 110, 108, 121, 32, 98, 121, 32, 96, 98, 97, 99, 107, 119, 97, 114, 100, 46, 112, 114, 105, 118, 97, 116, 101, 73, 110, 80, 117, 98, 108, 105, 99, 96, 32, 98, 101, 105, 110, 103, 32, 101, 110, 97, 98, 108, 101, 100, 46, 0]};
static mut l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value) as *mut leanh::LeanObject,4665502414017888213 as *mut leanh::LeanObject] };
static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value) as *mut leanh::LeanObject,6097534712086569347 as *mut leanh::LeanObject] };
static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value) as *mut leanh::LeanObject,10377308656794966622 as *mut leanh::LeanObject] };
pub static l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value) as *mut leanh::LeanObject,17610465030154420530 as *mut leanh::LeanObject] };
static mut l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_ResolveName_backward_privateInPublic_warn: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        76, 101, 97, 110, 46, 82, 101, 115, 111, 108, 118, 101, 78, 97, 109, 101, 0,
    ],
};
static mut l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1_value:
    leanh::LeanStringObject<45> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        76, 101, 97, 110, 46, 82, 101, 115, 111, 108, 118, 101, 78, 97, 109, 101, 46, 114, 101,
        115, 111, 108, 118, 101, 78, 97, 109, 101, 115, 112, 97, 99, 101, 85, 115, 105, 110, 103,
        83, 99, 111, 112, 101, 63, 0,
    ],
};
static mut l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2_value:
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
static mut l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
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
        80, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110,
        32, 96, 0,
    ],
};
static mut l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2_value:
    leanh::LeanStringObject<167> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 167,
    m_capacity: 167,
    m_length: 166,
    m_data: [
        96, 32, 97, 99, 99, 101, 115, 115, 101, 100, 32, 112, 117, 98, 108, 105, 99, 108, 121, 59,
        32, 116, 104, 105, 115, 32, 105, 115, 32, 97, 108, 108, 111, 119, 101, 100, 32, 111, 110,
        108, 121, 32, 98, 101, 99, 97, 117, 115, 101, 32, 116, 104, 101, 32, 96, 98, 97, 99, 107,
        119, 97, 114, 100, 46, 112, 114, 105, 118, 97, 116, 101, 73, 110, 80, 117, 98, 108, 105,
        99, 96, 32, 111, 112, 116, 105, 111, 110, 32, 105, 115, 32, 101, 110, 97, 98, 108, 101,
        100, 46, 32, 10, 10, 68, 105, 115, 97, 98, 108, 101, 32, 96, 98, 97, 99, 107, 119, 97, 114,
        100, 46, 112, 114, 105, 118, 97, 116, 101, 73, 110, 80, 117, 98, 108, 105, 99, 46, 119, 97,
        114, 110, 96, 32, 116, 111, 32, 115, 105, 108, 101, 110, 99, 101, 32, 116, 104, 105, 115,
        32, 119, 97, 114, 110, 105, 110, 103, 46, 0,
    ],
};
static mut l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_resolveGlobalName___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_resolveGlobalName___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_resolveGlobalName___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveGlobalName___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        117, 110, 107, 110, 111, 119, 110, 32, 110, 97, 109, 101, 115, 112, 97, 99, 101, 32, 96, 0,
    ],
};
static mut l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1_value:
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
static mut l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveNamespace___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_resolveNamespace___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_resolveNamespace___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveNamespace___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveNamespace___redArg___closed__1_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_resolveNamespace___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveNamespace___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveNamespace___redArg___closed__2_value: leanh::LeanStringObject<20> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            101, 120, 112, 101, 99, 116, 101, 100, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101,
            114, 0,
        ],
    };
static mut l_Lean_resolveNamespace___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveNamespace___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveNamespace___redArg___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_resolveNamespace___redArg___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_resolveNamespace___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveNamespace___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_resolveNamespace___redArg___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_resolveNamespace___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
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
        97, 109, 98, 105, 103, 117, 111, 117, 115, 32, 110, 97, 109, 101, 115, 112, 97, 99, 101,
        32, 96, 0,
    ],
};
static mut l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1_value:
    leanh::LeanStringObject<31> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        96, 44, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 105, 110, 116, 101, 114, 112, 114,
        101, 116, 97, 116, 105, 111, 110, 115, 58, 32, 96, 0,
    ],
};
static mut l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveUniqueNamespace___redArg___closed__0_value:
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
    m_fun: l_Lean_Name_instToString___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_resolveUniqueNamespace___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveUniqueNamespace___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_filterFieldList___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_filterFieldList___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_filterFieldList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_filterFieldList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_filterFieldList___redArg___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_filterFieldList___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_filterFieldList___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_filterFieldList___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ensureNoOverload___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_ensureNoOverload___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ensureNoOverload___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ensureNoOverload___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ensureNoOverload___redArg___closed__1_value: leanh::LeanStringObject<23> =
    leanh::LeanStringObject {
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
            65, 109, 98, 105, 103, 117, 111, 117, 115, 32, 105, 100, 101, 110, 116, 105, 102, 105,
            101, 114, 32, 96, 0,
        ],
    };
static mut l_Lean_ensureNoOverload___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ensureNoOverload___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_ensureNoOverload___redArg___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ensureNoOverload___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ensureNoOverload___redArg___closed__3_value: leanh::LeanStringObject<30> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            96, 59, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 105, 110, 116, 101, 114, 112,
            114, 101, 116, 97, 116, 105, 111, 110, 115, 58, 32, 0,
        ],
    };
static mut l_Lean_ensureNoOverload___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ensureNoOverload___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_ensureNoOverload___redArg___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ensureNoOverload___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ensureNoOverload___redArg___closed__5_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_MessageData_ofExpr as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ensureNoOverload___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ensureNoOverload___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_preprocessSyntaxAndResolve___redArg___closed__0_value:
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
    m_fun: l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_preprocessSyntaxAndResolve___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_preprocessSyntaxAndResolve___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ensureNonAmbiguous___redArg___closed__0_value: leanh::LeanStringObject<
    24,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        76, 101, 97, 110, 46, 101, 110, 115, 117, 114, 101, 78, 111, 110, 65, 109, 98, 105, 103,
        117, 111, 117, 115, 0,
    ],
};
static mut l_Lean_ensureNonAmbiguous___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ensureNonAmbiguous___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_ensureNonAmbiguous___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ensureNonAmbiguous___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ensureNonAmbiguous___redArg___closed__2_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Expr_dbgToString___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ensureNonAmbiguous___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ensureNonAmbiguous___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ensureNonAmbiguous___redArg___closed__3_value: leanh::LeanStringObject<
    23,
> = leanh::LeanStringObject {
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
        97, 109, 98, 105, 103, 117, 111, 117, 115, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101,
        114, 32, 96, 0,
    ],
};
static mut l_Lean_ensureNonAmbiguous___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ensureNonAmbiguous___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ensureNonAmbiguous___redArg___closed__4_value: leanh::LeanStringObject<
    30,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        96, 44, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 105, 110, 116, 101, 114, 112, 114,
        101, 116, 97, 116, 105, 111, 110, 115, 58, 32, 0,
    ],
};
static mut l_Lean_ensureNonAmbiguous___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ensureNonAmbiguous___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveLocalName___redArg___lam__3___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_resolveLocalName___redArg___lam__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___lam__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveLocalName___redArg___lam__3___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_resolveLocalName___redArg___lam__3___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___lam__3___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveLocalName___redArg___lam__3___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_resolveLocalName___redArg___lam__3___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___lam__3___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveLocalName___redArg___lam__3___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_resolveLocalName___redArg___lam__3___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___lam__3___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveLocalName___redArg___lam__3___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_resolveLocalName___redArg___lam__3___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___lam__3___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveLocalName___redArg___lam__3___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_resolveLocalName___redArg___lam__3___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___lam__3___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveLocalName___redArg___lam__3___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_resolveLocalName___redArg___lam__3___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___lam__3___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveLocalName___redArg___lam__3___closed__7_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___lam__3___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___lam__3___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_resolveLocalName___redArg___lam__3___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___lam__3___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveLocalName___redArg___lam__3___closed__8_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___lam__3___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___lam__3___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___lam__3___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___lam__3___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___lam__3___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_resolveLocalName___redArg___lam__3___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___lam__3___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveLocalName___redArg___lam__3___closed__9_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___lam__3___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___lam__3___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_resolveLocalName___redArg___lam__3___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___lam__3___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveLocalName___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_resolveLocalName___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_resolveLocalName___redArg___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_resolveLocalName___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_resolveLocalName___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_resolveLocalName___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0___closed__0_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_isNone___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3685_ = l_Lean_throwReservedNameNotAvailable___redArg___closed__0;
    v___x_3686_ = l_Lean_stringToMessageData(v___x_3685_);
    return v___x_3686_;
}
pub unsafe fn _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3688_ = l_Lean_throwReservedNameNotAvailable___redArg___closed__2;
    v___x_3689_ = l_Lean_stringToMessageData(v___x_3688_);
    return v___x_3689_;
}
pub unsafe fn _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3691_ = l_Lean_throwReservedNameNotAvailable___redArg___closed__4;
    v___x_3692_ = l_Lean_stringToMessageData(v___x_3691_);
    return v___x_3692_;
}
pub unsafe fn l_Lean_throwReservedNameNotAvailable___redArg(
    mut v_inst_3693_: *mut leanh::LeanObject,
    mut v_inst_3694_: *mut leanh::LeanObject,
    mut v_declName_3695_: *mut leanh::LeanObject,
    mut v_reservedName_3696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: u8 = 0;
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: u8 = 0;
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3697_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_throwReservedNameNotAvailable___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_throwReservedNameNotAvailable___redArg___closed__1_once),
        _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__1,
    );
    v___x_3698_ = 0;
    v___x_3699_ = l_Lean_MessageData_ofConstName(v_declName_3695_, v___x_3698_);
    v___x_3700_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3700_, 0, v___x_3697_);
    leanh::lean_ctor_set(v___x_3700_, 1, v___x_3699_);
    v___x_3701_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_throwReservedNameNotAvailable___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_throwReservedNameNotAvailable___redArg___closed__3_once),
        _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__3,
    );
    v___x_3702_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3702_, 0, v___x_3700_);
    leanh::lean_ctor_set(v___x_3702_, 1, v___x_3701_);
    v___x_3703_ = 1;
    v___x_3704_ = l_Lean_MessageData_ofConstName(v_reservedName_3696_, v___x_3703_);
    v___x_3705_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3705_, 0, v___x_3702_);
    leanh::lean_ctor_set(v___x_3705_, 1, v___x_3704_);
    v___x_3706_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_throwReservedNameNotAvailable___redArg___closed__5),
        core::ptr::addr_of_mut!(l_Lean_throwReservedNameNotAvailable___redArg___closed__5_once),
        _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__5,
    );
    v___x_3707_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3707_, 0, v___x_3705_);
    leanh::lean_ctor_set(v___x_3707_, 1, v___x_3706_);
    v___x_3708_ = l_Lean_throwError___redArg(v_inst_3693_, v_inst_3694_, v___x_3707_);
    return v___x_3708_;
}
pub unsafe fn l_Lean_throwReservedNameNotAvailable(
    mut v_m_3709_: *mut leanh::LeanObject,
    mut v_inst_3710_: *mut leanh::LeanObject,
    mut v_inst_3711_: *mut leanh::LeanObject,
    mut v_declName_3712_: *mut leanh::LeanObject,
    mut v_reservedName_3713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3714_ = l_Lean_throwReservedNameNotAvailable___redArg(
        v_inst_3710_,
        v_inst_3711_,
        v_declName_3712_,
        v_reservedName_3713_,
    );
    return v___x_3714_;
}
pub unsafe fn l_Lean_ensureReservedNameAvailable___redArg___lam__0(
    mut v_reservedName_3715_: *mut leanh::LeanObject,
    mut v_toApplicative_3716_: *mut leanh::LeanObject,
    mut v_inst_3717_: *mut leanh::LeanObject,
    mut v_inst_3718_: *mut leanh::LeanObject,
    mut v_declName_3719_: *mut leanh::LeanObject,
    mut v_____do__lift_3720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3721_: u8 = 0;
    let mut v___x_3722_: u8 = 0;
    v___x_3721_ = 1;
    leanh::lean_inc(v_reservedName_3715_);
    v___x_3722_ =
        l_Lean_Environment_contains(v_____do__lift_3720_, v_reservedName_3715_, v___x_3721_);
    if v___x_3722_ == 0 {
        let mut v_toPure_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_declName_3719_);
        leanh::lean_dec_ref(v_inst_3718_);
        leanh::lean_dec_ref(v_inst_3717_);
        leanh::lean_dec(v_reservedName_3715_);
        v_toPure_3723_ = leanh::lean_ctor_get(v_toApplicative_3716_, 1);
        leanh::lean_inc(v_toPure_3723_);
        leanh::lean_dec_ref(v_toApplicative_3716_);
        v___x_3724_ = leanh::lean_box(0);
        v___x_3725_ =
            leanh::lean_apply_2(v_toPure_3723_, leanh::lean_box(0), v___x_3724_);
        return v___x_3725_;
    } else {
        let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toApplicative_3716_);
        v___x_3726_ = l_Lean_throwReservedNameNotAvailable___redArg(
            v_inst_3717_,
            v_inst_3718_,
            v_declName_3719_,
            v_reservedName_3715_,
        );
        return v___x_3726_;
    }
}
pub unsafe fn l_Lean_ensureReservedNameAvailable___redArg(
    mut v_inst_3727_: *mut leanh::LeanObject,
    mut v_inst_3728_: *mut leanh::LeanObject,
    mut v_inst_3729_: *mut leanh::LeanObject,
    mut v_declName_3730_: *mut leanh::LeanObject,
    mut v_suffix_3731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reservedName_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3732_ = leanh::lean_ctor_get(v_inst_3727_, 0);
    leanh::lean_inc_ref(v_toApplicative_3732_);
    v_toBind_3733_ = leanh::lean_ctor_get(v_inst_3727_, 1);
    leanh::lean_inc(v_toBind_3733_);
    v_getEnv_3734_ = leanh::lean_ctor_get(v_inst_3728_, 0);
    leanh::lean_inc(v_getEnv_3734_);
    leanh::lean_dec_ref(v_inst_3728_);
    leanh::lean_inc(v_declName_3730_);
    v_reservedName_3735_ = l_Lean_Name_str___override(v_declName_3730_, v_suffix_3731_);
    v___f_3736_ = leanh::lean_alloc_closure(
        l_Lean_ensureReservedNameAvailable___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_3736_, 0, v_reservedName_3735_);
    leanh::lean_closure_set(v___f_3736_, 1, v_toApplicative_3732_);
    leanh::lean_closure_set(v___f_3736_, 2, v_inst_3727_);
    leanh::lean_closure_set(v___f_3736_, 3, v_inst_3729_);
    leanh::lean_closure_set(v___f_3736_, 4, v_declName_3730_);
    v___x_3737_ = leanh::lean_apply_4(
        v_toBind_3733_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_3734_,
        v___f_3736_,
    );
    return v___x_3737_;
}
pub unsafe fn l_Lean_ensureReservedNameAvailable(
    mut v_m_3738_: *mut leanh::LeanObject,
    mut v_inst_3739_: *mut leanh::LeanObject,
    mut v_inst_3740_: *mut leanh::LeanObject,
    mut v_inst_3741_: *mut leanh::LeanObject,
    mut v_declName_3742_: *mut leanh::LeanObject,
    mut v_suffix_3743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3744_ = l_Lean_ensureReservedNameAvailable___redArg(
        v_inst_3739_,
        v_inst_3740_,
        v_inst_3741_,
        v_declName_3742_,
        v_suffix_3743_,
    );
    return v___x_3744_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3748_ = l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_;
    v___x_3749_ = lean_st_mk_ref(v___x_3748_);
    v___x_3750_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3750_, 0, v___x_3749_);
    return v___x_3750_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2____boxed(
    mut v_a_3751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3752_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_();
    return v_res_3752_;
}
pub unsafe fn _init_l_Lean_registerReservedNamePredicate___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3754_ = l_Lean_registerReservedNamePredicate___closed__0;
    v___x_3755_ = lean_mk_io_user_error(v___x_3754_);
    return v___x_3755_;
}
pub unsafe fn l_Lean_registerReservedNamePredicate(
    mut v_p_3756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3762_: u8 = 0;
    let mut v___x_3763_: u8 = 0;
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3775_: u8 = 0;
    let mut v_a_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3779_: u8 = 0;
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3758_ = l_Lean_initializing();
                if leanh::lean_obj_tag(v___x_3758_) == 0 {
                    v_a_3759_ = leanh::lean_ctor_get(v___x_3758_, 0);
                    v_isSharedCheck_3775_ = (!leanh::lean_is_exclusive(v___x_3758_)) as u8;
                    if v_isSharedCheck_3775_ == 0 {
                        v___x_3761_ = v___x_3758_;
                        v_isShared_3762_ = v_isSharedCheck_3775_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3759_);
                        leanh::lean_dec(v___x_3758_);
                        v___x_3761_ = leanh::lean_box(0);
                        v_isShared_3762_ = v_isSharedCheck_3775_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_p_3756_);
                    v_a_3776_ = leanh::lean_ctor_get(v___x_3758_, 0);
                    v_isSharedCheck_3783_ = (!leanh::lean_is_exclusive(v___x_3758_)) as u8;
                    if v_isSharedCheck_3783_ == 0 {
                        v___x_3778_ = v___x_3758_;
                        v_isShared_3779_ = v_isSharedCheck_3783_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3776_);
                        leanh::lean_dec(v___x_3758_);
                        v___x_3778_ = leanh::lean_box(0);
                        v_isShared_3779_ = v_isSharedCheck_3783_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3763_ = (leanh::lean_unbox(v_a_3759_) as u8);
                leanh::lean_dec(v_a_3759_);
                if v___x_3763_ == 0 {
                    leanh::lean_dec_ref(v_p_3756_);
                    v___x_3764_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_registerReservedNamePredicate___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_registerReservedNamePredicate___closed__1_once
                        ),
                        _init_l_Lean_registerReservedNamePredicate___closed__1,
                    );
                    if v_isShared_3762_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3761_, 1);
                        leanh::lean_ctor_set(v___x_3761_, 0, v___x_3764_);
                        v___x_3766_ = v___x_3761_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3767_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3764_);
                        v___x_3766_ = v_reuseFailAlloc_3767_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3768_ = l_Lean_reservedNamePredicatesRef;
                    v___x_3769_ = lean_st_ref_take(v___x_3768_);
                    v___x_3770_ = lean_array_push(v___x_3769_, v_p_3756_);
                    v___x_3771_ = lean_st_ref_set(v___x_3768_, v___x_3770_);
                    if v_isShared_3762_ == 0 {
                        leanh::lean_ctor_set(v___x_3761_, 0, v___x_3771_);
                        v___x_3773_ = v___x_3761_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3774_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3771_);
                        v___x_3773_ = v_reuseFailAlloc_3774_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3766_;
            }
            3 => {
                return v___x_3773_;
            }
            4 => {
                if v_isShared_3779_ == 0 {
                    v___x_3781_ = v___x_3778_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3782_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
                    v___x_3781_ = v_reuseFailAlloc_3782_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3781_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_registerReservedNamePredicate___boxed(
    mut v_p_3784_: *mut leanh::LeanObject,
    mut v_a_3785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3786_ = l_Lean_registerReservedNamePredicate(v_p_3784_);
    return v_res_3786_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(
    mut v___x_3787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3789_ = lean_st_ref_get(v___x_3787_);
    v___x_3790_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3790_, 0, v___x_3789_);
    return v___x_3790_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed(
    mut v___x_3791_: *mut leanh::LeanObject,
    mut v___y_3792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3793_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(v___x_3791_);
    leanh::lean_dec(v___x_3791_);
    return v_res_3793_;
}
pub unsafe fn _init_l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3794_ = l_Lean_reservedNamePredicatesRef;
    v___f_3795_ = leanh::lean_alloc_closure(l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_3795_, 0, v___x_3794_);
    return v___f_3795_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3797_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2__once), _init_l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_);
    v___x_3798_ = leanh::lean_box(0);
    v___x_3799_ = leanh::lean_box(2);
    v___x_3800_ = l_Lean_registerEnvExtension___redArg(v___f_3797_, v___x_3798_, v___x_3799_);
    return v___x_3800_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed(
    mut v_a_3801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3802_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_();
    return v_res_3802_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(
    mut v_env_3803_: *mut leanh::LeanObject,
    mut v_name_3804_: *mut leanh::LeanObject,
    mut v_as_3805_: *mut leanh::LeanObject,
    mut v_i_3806_: usize,
    mut v_stop_3807_: usize,
) -> u8 {
    let mut v___x_3808_: u8 = 0;
    let mut v___x_161__overap_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: u8 = 0;
    let mut v___x_3812_: usize = 0;
    let mut v___x_3813_: usize = 0;
    let mut v___x_3815_: u8 = 0;
    let mut v___x_3816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3808_ = lean_usize_dec_eq(v_i_3806_, v_stop_3807_);
                if v___x_3808_ == 0 {
                    v___x_161__overap_3809_ = lean_array_uget_borrowed(v_as_3805_, v_i_3806_);
                    leanh::lean_inc(v___x_161__overap_3809_);
                    leanh::lean_inc(v_name_3804_);
                    leanh::lean_inc_ref(v_env_3803_);
                    v___x_3810_ = leanh::lean_apply_2(
                        v___x_161__overap_3809_,
                        v_env_3803_,
                        v_name_3804_,
                    );
                    v___x_3811_ = (leanh::lean_unbox(v___x_3810_) as u8);
                    if v___x_3811_ == 0 {
                        v___x_3812_ = 1usize;
                        v___x_3813_ = lean_usize_add(v_i_3806_, v___x_3812_);
                        v_i_3806_ = v___x_3813_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_name_3804_);
                        leanh::lean_dec_ref(v_env_3803_);
                        v___x_3815_ = (leanh::lean_unbox(v___x_3810_) as u8);
                        return v___x_3815_;
                    }
                } else {
                    leanh::lean_dec(v_name_3804_);
                    leanh::lean_dec_ref(v_env_3803_);
                    v___x_3816_ = 0;
                    return v___x_3816_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0___boxed(
    mut v_env_3817_: *mut leanh::LeanObject,
    mut v_name_3818_: *mut leanh::LeanObject,
    mut v_as_3819_: *mut leanh::LeanObject,
    mut v_i_3820_: *mut leanh::LeanObject,
    mut v_stop_3821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3822_: usize = 0;
    let mut v_stop_boxed_3823_: usize = 0;
    let mut v_res_3824_: u8 = 0;
    let mut v_r_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3822_ = leanh::lean_unbox_usize(v_i_3820_);
    leanh::lean_dec(v_i_3820_);
    v_stop_boxed_3823_ = leanh::lean_unbox_usize(v_stop_3821_);
    leanh::lean_dec(v_stop_3821_);
    v_res_3824_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(v_env_3817_, v_name_3818_, v_as_3819_, v_i_boxed_3822_, v_stop_boxed_3823_);
    leanh::lean_dec_ref(v_as_3819_);
    v_r_3825_ = leanh::lean_box((v_res_3824_) as usize);
    return v_r_3825_;
}
pub unsafe fn _init_l_Lean_isReservedName___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3826_ = l_Array_instInhabited(leanh::lean_box(0));
    return v___x_3826_;
}
pub unsafe fn lean_is_reserved_name(
    mut v_env_3827_: *mut leanh::LeanObject,
    mut v_name_3828_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: u8 = 0;
    v___x_3829_ = l_Lean_reservedNamePredicatesExt;
    v_asyncMode_3830_ = leanh::lean_ctor_get(v___x_3829_, 2);
    v___x_3831_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_isReservedName___closed__0),
        core::ptr::addr_of_mut!(l_Lean_isReservedName___closed__0_once),
        _init_l_Lean_isReservedName___closed__0,
    );
    v___x_3832_ = leanh::lean_box(0);
    leanh::lean_inc_ref(v_env_3827_);
    v___x_3833_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_3831_,
        v___x_3829_,
        v_env_3827_,
        v_asyncMode_3830_,
        v___x_3832_,
    );
    v___x_3834_ = leanh::lean_unsigned_to_nat(0);
    v___x_3835_ = lean_array_get_size(v___x_3833_);
    v___x_3836_ = lean_nat_dec_lt(v___x_3834_, v___x_3835_);
    if v___x_3836_ == 0 {
        leanh::lean_dec(v___x_3833_);
        leanh::lean_dec(v_name_3828_);
        leanh::lean_dec_ref(v_env_3827_);
        return v___x_3836_;
    } else {
        if v___x_3836_ == 0 {
            leanh::lean_dec(v___x_3833_);
            leanh::lean_dec(v_name_3828_);
            leanh::lean_dec_ref(v_env_3827_);
            return v___x_3836_;
        } else {
            let mut v___x_3837_: usize = 0;
            let mut v___x_3838_: usize = 0;
            let mut v___x_3839_: u8 = 0;
            v___x_3837_ = 0usize;
            v___x_3838_ = lean_usize_of_nat(v___x_3835_);
            v___x_3839_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(v_env_3827_, v_name_3828_, v___x_3833_, v___x_3837_, v___x_3838_);
            leanh::lean_dec(v___x_3833_);
            return v___x_3839_;
        }
    }
}
pub unsafe fn l_Lean_isReservedName___boxed(
    mut v_env_3840_: *mut leanh::LeanObject,
    mut v_name_3841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3842_: u8 = 0;
    let mut v_r_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3842_ = lean_is_reserved_name(v_env_3840_, v_name_3841_);
    v_r_3843_ = leanh::lean_box((v_res_3842_) as usize);
    return v_r_3843_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(
    mut v_x_3844_: *mut leanh::LeanObject,
    mut v_x_3845_: *mut leanh::LeanObject,
    mut v_x_3846_: *mut leanh::LeanObject,
    mut v_x_3847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3852_: u8 = 0;
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: u8 = 0;
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: u8 = 0;
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3848_ = leanh::lean_ctor_get(v_x_3844_, 0);
                v_vs_3849_ = leanh::lean_ctor_get(v_x_3844_, 1);
                v_isSharedCheck_3873_ = (!leanh::lean_is_exclusive(v_x_3844_)) as u8;
                if v_isSharedCheck_3873_ == 0 {
                    v___x_3851_ = v_x_3844_;
                    v_isShared_3852_ = v_isSharedCheck_3873_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_3849_);
                    leanh::lean_inc(v_ks_3848_);
                    leanh::lean_dec(v_x_3844_);
                    v___x_3851_ = leanh::lean_box(0);
                    v_isShared_3852_ = v_isSharedCheck_3873_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3853_ = lean_array_get_size(v_ks_3848_);
                v___x_3854_ = lean_nat_dec_lt(v_x_3845_, v___x_3853_);
                if v___x_3854_ == 0 {
                    leanh::lean_dec(v_x_3845_);
                    v___x_3855_ = lean_array_push(v_ks_3848_, v_x_3846_);
                    v___x_3856_ = lean_array_push(v_vs_3849_, v_x_3847_);
                    if v_isShared_3852_ == 0 {
                        leanh::lean_ctor_set(v___x_3851_, 1, v___x_3856_);
                        leanh::lean_ctor_set(v___x_3851_, 0, v___x_3855_);
                        v___x_3858_ = v___x_3851_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3859_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3855_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3859_, 1, v___x_3856_);
                        v___x_3858_ = v_reuseFailAlloc_3859_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3860_ = lean_array_fget_borrowed(v_ks_3848_, v_x_3845_);
                    v___x_3861_ = lean_name_eq(v_x_3846_, v_k_x27_3860_);
                    if v___x_3861_ == 0 {
                        if v_isShared_3852_ == 0 {
                            v___x_3863_ = v___x_3851_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3867_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_ks_3848_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3867_, 1, v_vs_3849_);
                            v___x_3863_ = v_reuseFailAlloc_3867_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3868_ = lean_array_fset(v_ks_3848_, v_x_3845_, v_x_3846_);
                        v___x_3869_ = lean_array_fset(v_vs_3849_, v_x_3845_, v_x_3847_);
                        leanh::lean_dec(v_x_3845_);
                        if v_isShared_3852_ == 0 {
                            leanh::lean_ctor_set(v___x_3851_, 1, v___x_3869_);
                            leanh::lean_ctor_set(v___x_3851_, 0, v___x_3868_);
                            v___x_3871_ = v___x_3851_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3872_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3868_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3872_, 1, v___x_3869_);
                            v___x_3871_ = v_reuseFailAlloc_3872_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3858_;
            }
            3 => {
                v___x_3864_ = leanh::lean_unsigned_to_nat(1);
                v___x_3865_ = lean_nat_add(v_x_3845_, v___x_3864_);
                leanh::lean_dec(v_x_3845_);
                v_x_3844_ = v___x_3863_;
                v_x_3845_ = v___x_3865_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3871_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(
    mut v_n_3874_: *mut leanh::LeanObject,
    mut v_k_3875_: *mut leanh::LeanObject,
    mut v_v_3876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3877_ = leanh::lean_unsigned_to_nat(0);
    v___x_3878_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_n_3874_, v___x_3877_, v_k_3875_, v_v_3876_);
    return v___x_3878_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0()
-> u64 {
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: u64 = 0;
    v___x_3879_ = leanh::lean_unsigned_to_nat(1723);
    v___x_3880_ = lean_uint64_of_nat(v___x_3879_);
    return v___x_3880_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0()
-> usize {
    let mut v___x_3881_: usize = 0;
    let mut v___x_3882_: usize = 0;
    let mut v___x_3883_: usize = 0;
    v___x_3881_ = 5usize;
    v___x_3882_ = 1usize;
    v___x_3883_ = lean_usize_shift_left(v___x_3882_, v___x_3881_);
    return v___x_3883_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__1()
-> usize {
    let mut v___x_3884_: usize = 0;
    let mut v___x_3885_: usize = 0;
    let mut v___x_3886_: usize = 0;
    v___x_3884_ = 1usize;
    v___x_3885_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0);
    v___x_3886_ = lean_usize_sub(v___x_3885_, v___x_3884_);
    return v___x_3886_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3887_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3887_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(
    mut v_x_3888_: *mut leanh::LeanObject,
    mut v_x_3889_: usize,
    mut v_x_3890_: usize,
    mut v_x_3891_: *mut leanh::LeanObject,
    mut v_x_3892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: usize = 0;
    let mut v___x_3895_: usize = 0;
    let mut v___x_3896_: usize = 0;
    let mut v___x_3897_: usize = 0;
    let mut v_j_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: u8 = 0;
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3903_: u8 = 0;
    let mut v_v_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3917_: u8 = 0;
    let mut v___x_3918_: u8 = 0;
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3924_: u8 = 0;
    let mut v_node_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3928_: u8 = 0;
    let mut v___x_3929_: usize = 0;
    let mut v___x_3930_: usize = 0;
    let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3935_: u8 = 0;
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3937_: u8 = 0;
    let mut v_unused_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3943_: u8 = 0;
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3948_: u8 = 0;
    let mut v_ks_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: usize = 0;
    let mut v___x_3955_: u8 = 0;
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: u8 = 0;
    let mut v_reuseFailAlloc_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3960_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3888_) == 0 {
                    v_es_3893_ = leanh::lean_ctor_get(v_x_3888_, 0);
                    v___x_3894_ = 5usize;
                    v___x_3895_ = 1usize;
                    v___x_3896_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__1);
                    v___x_3897_ = lean_usize_land(v_x_3889_, v___x_3896_);
                    v_j_3898_ = lean_usize_to_nat(v___x_3897_);
                    v___x_3899_ = lean_array_get_size(v_es_3893_);
                    v___x_3900_ = lean_nat_dec_lt(v_j_3898_, v___x_3899_);
                    if v___x_3900_ == 0 {
                        leanh::lean_dec(v_j_3898_);
                        leanh::lean_dec(v_x_3892_);
                        leanh::lean_dec(v_x_3891_);
                        return v_x_3888_;
                    } else {
                        leanh::lean_inc_ref(v_es_3893_);
                        v_isSharedCheck_3937_ = (!leanh::lean_is_exclusive(v_x_3888_)) as u8;
                        if v_isSharedCheck_3937_ == 0 {
                            v_unused_3938_ = leanh::lean_ctor_get(v_x_3888_, 0);
                            leanh::lean_dec(v_unused_3938_);
                            v___x_3902_ = v_x_3888_;
                            v_isShared_3903_ = v_isSharedCheck_3937_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_3888_);
                            v___x_3902_ = leanh::lean_box(0);
                            v_isShared_3903_ = v_isSharedCheck_3937_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3939_ = leanh::lean_ctor_get(v_x_3888_, 0);
                    v_vs_3940_ = leanh::lean_ctor_get(v_x_3888_, 1);
                    v_isSharedCheck_3960_ = (!leanh::lean_is_exclusive(v_x_3888_)) as u8;
                    if v_isSharedCheck_3960_ == 0 {
                        v___x_3942_ = v_x_3888_;
                        v_isShared_3943_ = v_isSharedCheck_3960_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_3940_);
                        leanh::lean_inc(v_ks_3939_);
                        leanh::lean_dec(v_x_3888_);
                        v___x_3942_ = leanh::lean_box(0);
                        v_isShared_3943_ = v_isSharedCheck_3960_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3904_ = lean_array_fget(v_es_3893_, v_j_3898_);
                v___x_3905_ = leanh::lean_box(0);
                v_xs_x27_3906_ = lean_array_fset(v_es_3893_, v_j_3898_, v___x_3905_);
                match leanh::lean_obj_tag(v_v_3904_) {
                    0 => {
                        v_key_3913_ = leanh::lean_ctor_get(v_v_3904_, 0);
                        v_val_3914_ = leanh::lean_ctor_get(v_v_3904_, 1);
                        v_isSharedCheck_3924_ = (!leanh::lean_is_exclusive(v_v_3904_)) as u8;
                        if v_isSharedCheck_3924_ == 0 {
                            v___x_3916_ = v_v_3904_;
                            v_isShared_3917_ = v_isSharedCheck_3924_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3914_);
                            leanh::lean_inc(v_key_3913_);
                            leanh::lean_dec(v_v_3904_);
                            v___x_3916_ = leanh::lean_box(0);
                            v_isShared_3917_ = v_isSharedCheck_3924_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3925_ = leanh::lean_ctor_get(v_v_3904_, 0);
                        v_isSharedCheck_3935_ = (!leanh::lean_is_exclusive(v_v_3904_)) as u8;
                        if v_isSharedCheck_3935_ == 0 {
                            v___x_3927_ = v_v_3904_;
                            v_isShared_3928_ = v_isSharedCheck_3935_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_3925_);
                            leanh::lean_dec(v_v_3904_);
                            v___x_3927_ = leanh::lean_box(0);
                            v_isShared_3928_ = v_isSharedCheck_3935_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3936_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3936_, 0, v_x_3891_);
                        leanh::lean_ctor_set(v___x_3936_, 1, v_x_3892_);
                        v___y_3908_ = v___x_3936_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3909_ = lean_array_fset(v_xs_x27_3906_, v_j_3898_, v___y_3908_);
                leanh::lean_dec(v_j_3898_);
                if v_isShared_3903_ == 0 {
                    leanh::lean_ctor_set(v___x_3902_, 0, v___x_3909_);
                    v___x_3911_ = v___x_3902_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3912_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3909_);
                    v___x_3911_ = v_reuseFailAlloc_3912_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3911_;
            }
            4 => {
                v___x_3918_ = lean_name_eq(v_x_3891_, v_key_3913_);
                if v___x_3918_ == 0 {
                    leanh::lean_del_object(v___x_3916_);
                    v___x_3919_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3913_,
                        v_val_3914_,
                        v_x_3891_,
                        v_x_3892_,
                    );
                    v___x_3920_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3920_, 0, v___x_3919_);
                    v___y_3908_ = v___x_3920_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_3914_);
                    leanh::lean_dec(v_key_3913_);
                    if v_isShared_3917_ == 0 {
                        leanh::lean_ctor_set(v___x_3916_, 1, v_x_3892_);
                        leanh::lean_ctor_set(v___x_3916_, 0, v_x_3891_);
                        v___x_3922_ = v___x_3916_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3923_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_x_3891_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3923_, 1, v_x_3892_);
                        v___x_3922_ = v_reuseFailAlloc_3923_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3908_ = v___x_3922_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3929_ = lean_usize_shift_right(v_x_3889_, v___x_3894_);
                v___x_3930_ = lean_usize_add(v_x_3890_, v___x_3895_);
                v___x_3931_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_node_3925_, v___x_3929_, v___x_3930_, v_x_3891_, v_x_3892_);
                if v_isShared_3928_ == 0 {
                    leanh::lean_ctor_set(v___x_3927_, 0, v___x_3931_);
                    v___x_3933_ = v___x_3927_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3934_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3931_);
                    v___x_3933_ = v_reuseFailAlloc_3934_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3908_ = v___x_3933_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3943_ == 0 {
                    v___x_3945_ = v___x_3942_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3959_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_ks_3939_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3959_, 1, v_vs_3940_);
                    v___x_3945_ = v_reuseFailAlloc_3959_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3946_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v___x_3945_, v_x_3891_, v_x_3892_);
                v___x_3954_ = 7usize;
                v___x_3955_ = lean_usize_dec_le(v___x_3954_, v_x_3890_);
                if v___x_3955_ == 0 {
                    v___x_3956_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3946_);
                    v___x_3957_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3958_ = lean_nat_dec_lt(v___x_3956_, v___x_3957_);
                    leanh::lean_dec(v___x_3956_);
                    v___y_3948_ = v___x_3958_;
                    state = 10;
                    continue;
                } else {
                    v___y_3948_ = v___x_3955_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3948_ == 0 {
                    v_ks_3949_ = leanh::lean_ctor_get(v_newNode_3946_, 0);
                    leanh::lean_inc_ref(v_ks_3949_);
                    v_vs_3950_ = leanh::lean_ctor_get(v_newNode_3946_, 1);
                    leanh::lean_inc_ref(v_vs_3950_);
                    leanh::lean_dec_ref(v_newNode_3946_);
                    v___x_3951_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3952_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__2);
                    v___x_3953_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_x_3890_, v_ks_3949_, v_vs_3950_, v___x_3951_, v___x_3952_);
                    leanh::lean_dec_ref(v_vs_3950_);
                    leanh::lean_dec_ref(v_ks_3949_);
                    return v___x_3953_;
                } else {
                    return v_newNode_3946_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(
    mut v_depth_3961_: usize,
    mut v_keys_3962_: *mut leanh::LeanObject,
    mut v_vals_3963_: *mut leanh::LeanObject,
    mut v_i_3964_: *mut leanh::LeanObject,
    mut v_entries_3965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: u8 = 0;
    let mut v_k_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3971_: u64 = 0;
    let mut v_h_3972_: usize = 0;
    let mut v___x_3973_: usize = 0;
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: usize = 0;
    let mut v___x_3976_: usize = 0;
    let mut v___x_3977_: usize = 0;
    let mut v_h_3978_: usize = 0;
    let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: u64 = 0;
    let mut v_hash_3983_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3966_ = lean_array_get_size(v_keys_3962_);
                v___x_3967_ = lean_nat_dec_lt(v_i_3964_, v___x_3966_);
                if v___x_3967_ == 0 {
                    leanh::lean_dec(v_i_3964_);
                    return v_entries_3965_;
                } else {
                    v_k_3968_ = lean_array_fget_borrowed(v_keys_3962_, v_i_3964_);
                    v_v_3969_ = lean_array_fget_borrowed(v_vals_3963_, v_i_3964_);
                    if leanh::lean_obj_tag(v_k_3968_) == 0 {
                        v___x_3982_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
                        v___y_3971_ = v___x_3982_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_3983_ = leanh::lean_ctor_get_uint64(
                            v_k_3968_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_3971_ = v_hash_3983_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_3972_ = lean_uint64_to_usize(v___y_3971_);
                v___x_3973_ = 5usize;
                v___x_3974_ = leanh::lean_unsigned_to_nat(1);
                v___x_3975_ = 1usize;
                v___x_3976_ = lean_usize_sub(v_depth_3961_, v___x_3975_);
                v___x_3977_ = lean_usize_mul(v___x_3973_, v___x_3976_);
                v_h_3978_ = lean_usize_shift_right(v_h_3972_, v___x_3977_);
                v___x_3979_ = lean_nat_add(v_i_3964_, v___x_3974_);
                leanh::lean_dec(v_i_3964_);
                leanh::lean_inc(v_v_3969_);
                leanh::lean_inc(v_k_3968_);
                v___x_3980_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_entries_3965_, v_h_3978_, v_depth_3961_, v_k_3968_, v_v_3969_);
                v_i_3964_ = v___x_3979_;
                v_entries_3965_ = v___x_3980_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___boxed(
    mut v_depth_3984_: *mut leanh::LeanObject,
    mut v_keys_3985_: *mut leanh::LeanObject,
    mut v_vals_3986_: *mut leanh::LeanObject,
    mut v_i_3987_: *mut leanh::LeanObject,
    mut v_entries_3988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3989_: usize = 0;
    let mut v_res_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3989_ = leanh::lean_unbox_usize(v_depth_3984_);
    leanh::lean_dec(v_depth_3984_);
    v_res_3990_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_boxed_3989_, v_keys_3985_, v_vals_3986_, v_i_3987_, v_entries_3988_);
    leanh::lean_dec_ref(v_vals_3986_);
    leanh::lean_dec_ref(v_keys_3985_);
    return v_res_3990_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___boxed(
    mut v_x_3991_: *mut leanh::LeanObject,
    mut v_x_3992_: *mut leanh::LeanObject,
    mut v_x_3993_: *mut leanh::LeanObject,
    mut v_x_3994_: *mut leanh::LeanObject,
    mut v_x_3995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1112__boxed_3996_: usize = 0;
    let mut v_x_1113__boxed_3997_: usize = 0;
    let mut v_res_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1112__boxed_3996_ = leanh::lean_unbox_usize(v_x_3992_);
    leanh::lean_dec(v_x_3992_);
    v_x_1113__boxed_3997_ = leanh::lean_unbox_usize(v_x_3993_);
    leanh::lean_dec(v_x_3993_);
    v_res_3998_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_3991_, v_x_1112__boxed_3996_, v_x_1113__boxed_3997_, v_x_3994_, v_x_3995_);
    return v_res_3998_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(
    mut v_x_3999_: *mut leanh::LeanObject,
    mut v_x_4000_: *mut leanh::LeanObject,
    mut v_x_4001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4003_: u64 = 0;
    let mut v___x_4004_: usize = 0;
    let mut v___x_4005_: usize = 0;
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: u64 = 0;
    let mut v_hash_4008_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4000_) == 0 {
                    v___x_4007_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
                    v___y_4003_ = v___x_4007_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4008_ = leanh::lean_ctor_get_uint64(
                        v_x_4000_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4003_ = v_hash_4008_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4004_ = lean_uint64_to_usize(v___y_4003_);
                v___x_4005_ = 1usize;
                v___x_4006_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_3999_, v___x_4004_, v___x_4005_, v_x_4000_, v_x_4001_);
                return v___x_4006_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(
    mut v_x_4009_: *mut leanh::LeanObject,
    mut v_x_4010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4016_: u8 = 0;
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4019_: u64 = 0;
    let mut v___x_4020_: u64 = 0;
    let mut v___x_4021_: u64 = 0;
    let mut v_fold_4022_: u64 = 0;
    let mut v___x_4023_: u64 = 0;
    let mut v___x_4024_: u64 = 0;
    let mut v___x_4025_: u64 = 0;
    let mut v___x_4026_: usize = 0;
    let mut v___x_4027_: usize = 0;
    let mut v___x_4028_: usize = 0;
    let mut v___x_4029_: usize = 0;
    let mut v___x_4030_: usize = 0;
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: u64 = 0;
    let mut v_hash_4038_: u64 = 0;
    let mut v_isSharedCheck_4039_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4010_) == 0 {
                    return v_x_4009_;
                } else {
                    v_key_4011_ = leanh::lean_ctor_get(v_x_4010_, 0);
                    v_value_4012_ = leanh::lean_ctor_get(v_x_4010_, 1);
                    v_tail_4013_ = leanh::lean_ctor_get(v_x_4010_, 2);
                    v_isSharedCheck_4039_ = (!leanh::lean_is_exclusive(v_x_4010_)) as u8;
                    if v_isSharedCheck_4039_ == 0 {
                        v___x_4015_ = v_x_4010_;
                        v_isShared_4016_ = v_isSharedCheck_4039_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4013_);
                        leanh::lean_inc(v_value_4012_);
                        leanh::lean_inc(v_key_4011_);
                        leanh::lean_dec(v_x_4010_);
                        v___x_4015_ = leanh::lean_box(0);
                        v_isShared_4016_ = v_isSharedCheck_4039_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4017_ = lean_array_get_size(v_x_4009_);
                if leanh::lean_obj_tag(v_key_4011_) == 0 {
                    v___x_4037_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
                    v___y_4019_ = v___x_4037_;
                    state = 2;
                    continue;
                } else {
                    v_hash_4038_ = leanh::lean_ctor_get_uint64(
                        v_key_4011_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4019_ = v_hash_4038_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4020_ = 32u64;
                v___x_4021_ = lean_uint64_shift_right(v___y_4019_, v___x_4020_);
                v_fold_4022_ = lean_uint64_xor(v___y_4019_, v___x_4021_);
                v___x_4023_ = 16u64;
                v___x_4024_ = lean_uint64_shift_right(v_fold_4022_, v___x_4023_);
                v___x_4025_ = lean_uint64_xor(v_fold_4022_, v___x_4024_);
                v___x_4026_ = lean_uint64_to_usize(v___x_4025_);
                v___x_4027_ = lean_usize_of_nat(v___x_4017_);
                v___x_4028_ = 1usize;
                v___x_4029_ = lean_usize_sub(v___x_4027_, v___x_4028_);
                v___x_4030_ = lean_usize_land(v___x_4026_, v___x_4029_);
                v___x_4031_ = lean_array_uget_borrowed(v_x_4009_, v___x_4030_);
                leanh::lean_inc(v___x_4031_);
                if v_isShared_4016_ == 0 {
                    leanh::lean_ctor_set(v___x_4015_, 2, v___x_4031_);
                    v___x_4033_ = v___x_4015_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4036_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_key_4011_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4036_, 1, v_value_4012_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4036_, 2, v___x_4031_);
                    v___x_4033_ = v_reuseFailAlloc_4036_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4034_ = lean_array_uset(v_x_4009_, v___x_4030_, v___x_4033_);
                v_x_4009_ = v___x_4034_;
                v_x_4010_ = v_tail_4013_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(
    mut v_i_4040_: *mut leanh::LeanObject,
    mut v_source_4041_: *mut leanh::LeanObject,
    mut v_target_4042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: u8 = 0;
    let mut v_es_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4043_ = lean_array_get_size(v_source_4041_);
                v___x_4044_ = lean_nat_dec_lt(v_i_4040_, v___x_4043_);
                if v___x_4044_ == 0 {
                    leanh::lean_dec_ref(v_source_4041_);
                    leanh::lean_dec(v_i_4040_);
                    return v_target_4042_;
                } else {
                    v_es_4045_ = lean_array_fget(v_source_4041_, v_i_4040_);
                    v___x_4046_ = leanh::lean_box(0);
                    v_source_4047_ = lean_array_fset(v_source_4041_, v_i_4040_, v___x_4046_);
                    v_target_4048_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_target_4042_, v_es_4045_);
                    v___x_4049_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4050_ = lean_nat_add(v_i_4040_, v___x_4049_);
                    leanh::lean_dec(v_i_4040_);
                    v_i_4040_ = v___x_4050_;
                    v_source_4041_ = v_source_4047_;
                    v_target_4042_ = v_target_4048_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(
    mut v_data_4052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4053_ = lean_array_get_size(v_data_4052_);
    v___x_4054_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4055_ = lean_nat_mul(v___x_4053_, v___x_4054_);
    v___x_4056_ = leanh::lean_unsigned_to_nat(0);
    v___x_4057_ = leanh::lean_box(0);
    v___x_4058_ = lean_mk_array(v_nbuckets_4055_, v___x_4057_);
    v___x_4059_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v___x_4056_, v_data_4052_, v___x_4058_);
    return v___x_4059_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(
    mut v_a_4060_: *mut leanh::LeanObject,
    mut v_x_4061_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4062_: u8 = 0;
    let mut v_key_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4061_) == 0 {
                    v___x_4062_ = 0;
                    return v___x_4062_;
                } else {
                    v_key_4063_ = leanh::lean_ctor_get(v_x_4061_, 0);
                    v_tail_4064_ = leanh::lean_ctor_get(v_x_4061_, 2);
                    v___x_4065_ = lean_name_eq(v_key_4063_, v_a_4060_);
                    if v___x_4065_ == 0 {
                        v_x_4061_ = v_tail_4064_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4065_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___boxed(
    mut v_a_4067_: *mut leanh::LeanObject,
    mut v_x_4068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4069_: u8 = 0;
    let mut v_r_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4069_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_4067_, v_x_4068_);
    leanh::lean_dec(v_x_4068_);
    leanh::lean_dec(v_a_4067_);
    v_r_4070_ = leanh::lean_box((v_res_4069_) as usize);
    return v_r_4070_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(
    mut v_a_4071_: *mut leanh::LeanObject,
    mut v_b_4072_: *mut leanh::LeanObject,
    mut v_x_4073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4079_: u8 = 0;
    let mut v___x_4080_: u8 = 0;
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4088_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4073_) == 0 {
                    leanh::lean_dec(v_b_4072_);
                    leanh::lean_dec(v_a_4071_);
                    return v_x_4073_;
                } else {
                    v_key_4074_ = leanh::lean_ctor_get(v_x_4073_, 0);
                    v_value_4075_ = leanh::lean_ctor_get(v_x_4073_, 1);
                    v_tail_4076_ = leanh::lean_ctor_get(v_x_4073_, 2);
                    v_isSharedCheck_4088_ = (!leanh::lean_is_exclusive(v_x_4073_)) as u8;
                    if v_isSharedCheck_4088_ == 0 {
                        v___x_4078_ = v_x_4073_;
                        v_isShared_4079_ = v_isSharedCheck_4088_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4076_);
                        leanh::lean_inc(v_value_4075_);
                        leanh::lean_inc(v_key_4074_);
                        leanh::lean_dec(v_x_4073_);
                        v___x_4078_ = leanh::lean_box(0);
                        v_isShared_4079_ = v_isSharedCheck_4088_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4080_ = lean_name_eq(v_key_4074_, v_a_4071_);
                if v___x_4080_ == 0 {
                    v___x_4081_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_4071_, v_b_4072_, v_tail_4076_);
                    if v_isShared_4079_ == 0 {
                        leanh::lean_ctor_set(v___x_4078_, 2, v___x_4081_);
                        v___x_4083_ = v___x_4078_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4084_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_key_4074_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4084_, 1, v_value_4075_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4084_, 2, v___x_4081_);
                        v___x_4083_ = v_reuseFailAlloc_4084_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_4075_);
                    leanh::lean_dec(v_key_4074_);
                    if v_isShared_4079_ == 0 {
                        leanh::lean_ctor_set(v___x_4078_, 1, v_b_4072_);
                        leanh::lean_ctor_set(v___x_4078_, 0, v_a_4071_);
                        v___x_4086_ = v___x_4078_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4087_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4071_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4087_, 1, v_b_4072_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4087_, 2, v_tail_4076_);
                        v___x_4086_ = v_reuseFailAlloc_4087_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4083_;
            }
            3 => {
                return v___x_4086_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(
    mut v_m_4089_: *mut leanh::LeanObject,
    mut v_a_4090_: *mut leanh::LeanObject,
    mut v_b_4091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4096_: u8 = 0;
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4099_: u64 = 0;
    let mut v___x_4100_: u64 = 0;
    let mut v___x_4101_: u64 = 0;
    let mut v_fold_4102_: u64 = 0;
    let mut v___x_4103_: u64 = 0;
    let mut v___x_4104_: u64 = 0;
    let mut v___x_4105_: u64 = 0;
    let mut v___x_4106_: usize = 0;
    let mut v___x_4107_: usize = 0;
    let mut v___x_4108_: usize = 0;
    let mut v___x_4109_: usize = 0;
    let mut v___x_4110_: usize = 0;
    let mut v_bkt_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: u8 = 0;
    let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: u8 = 0;
    let mut v_val_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: u64 = 0;
    let mut v_hash_4138_: u64 = 0;
    let mut v_isSharedCheck_4139_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4092_ = leanh::lean_ctor_get(v_m_4089_, 0);
                v_buckets_4093_ = leanh::lean_ctor_get(v_m_4089_, 1);
                v_isSharedCheck_4139_ = (!leanh::lean_is_exclusive(v_m_4089_)) as u8;
                if v_isSharedCheck_4139_ == 0 {
                    v___x_4095_ = v_m_4089_;
                    v_isShared_4096_ = v_isSharedCheck_4139_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_4093_);
                    leanh::lean_inc(v_size_4092_);
                    leanh::lean_dec(v_m_4089_);
                    v___x_4095_ = leanh::lean_box(0);
                    v_isShared_4096_ = v_isSharedCheck_4139_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4097_ = lean_array_get_size(v_buckets_4093_);
                if leanh::lean_obj_tag(v_a_4090_) == 0 {
                    v___x_4137_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
                    v___y_4099_ = v___x_4137_;
                    state = 2;
                    continue;
                } else {
                    v_hash_4138_ = leanh::lean_ctor_get_uint64(
                        v_a_4090_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4099_ = v_hash_4138_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4100_ = 32u64;
                v___x_4101_ = lean_uint64_shift_right(v___y_4099_, v___x_4100_);
                v_fold_4102_ = lean_uint64_xor(v___y_4099_, v___x_4101_);
                v___x_4103_ = 16u64;
                v___x_4104_ = lean_uint64_shift_right(v_fold_4102_, v___x_4103_);
                v___x_4105_ = lean_uint64_xor(v_fold_4102_, v___x_4104_);
                v___x_4106_ = lean_uint64_to_usize(v___x_4105_);
                v___x_4107_ = lean_usize_of_nat(v___x_4097_);
                v___x_4108_ = 1usize;
                v___x_4109_ = lean_usize_sub(v___x_4107_, v___x_4108_);
                v___x_4110_ = lean_usize_land(v___x_4106_, v___x_4109_);
                v_bkt_4111_ = lean_array_uget_borrowed(v_buckets_4093_, v___x_4110_);
                v___x_4112_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_4090_, v_bkt_4111_);
                if v___x_4112_ == 0 {
                    v___x_4113_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_4114_ = lean_nat_add(v_size_4092_, v___x_4113_);
                    leanh::lean_dec(v_size_4092_);
                    leanh::lean_inc(v_bkt_4111_);
                    v___x_4115_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_4115_, 0, v_a_4090_);
                    leanh::lean_ctor_set(v___x_4115_, 1, v_b_4091_);
                    leanh::lean_ctor_set(v___x_4115_, 2, v_bkt_4111_);
                    v_buckets_x27_4116_ =
                        lean_array_uset(v_buckets_4093_, v___x_4110_, v___x_4115_);
                    v___x_4117_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4118_ = lean_nat_mul(v_size_x27_4114_, v___x_4117_);
                    v___x_4119_ = leanh::lean_unsigned_to_nat(3);
                    v___x_4120_ = lean_nat_div(v___x_4118_, v___x_4119_);
                    leanh::lean_dec(v___x_4118_);
                    v___x_4121_ = lean_array_get_size(v_buckets_x27_4116_);
                    v___x_4122_ = lean_nat_dec_le(v___x_4120_, v___x_4121_);
                    leanh::lean_dec(v___x_4120_);
                    if v___x_4122_ == 0 {
                        v_val_4123_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_buckets_x27_4116_);
                        if v_isShared_4096_ == 0 {
                            leanh::lean_ctor_set(v___x_4095_, 1, v_val_4123_);
                            leanh::lean_ctor_set(v___x_4095_, 0, v_size_x27_4114_);
                            v___x_4125_ = v___x_4095_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4126_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_4126_,
                                0,
                                v_size_x27_4114_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_4126_, 1, v_val_4123_);
                            v___x_4125_ = v_reuseFailAlloc_4126_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_4096_ == 0 {
                            leanh::lean_ctor_set(v___x_4095_, 1, v_buckets_x27_4116_);
                            leanh::lean_ctor_set(v___x_4095_, 0, v_size_x27_4114_);
                            v___x_4128_ = v___x_4095_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4129_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_4129_,
                                0,
                                v_size_x27_4114_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_4129_,
                                1,
                                v_buckets_x27_4116_,
                            );
                            v___x_4128_ = v_reuseFailAlloc_4129_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_4111_);
                    v___x_4130_ = leanh::lean_box(0);
                    v_buckets_x27_4131_ =
                        lean_array_uset(v_buckets_4093_, v___x_4110_, v___x_4130_);
                    v___x_4132_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_4090_, v_b_4091_, v_bkt_4111_);
                    v___x_4133_ = lean_array_uset(v_buckets_x27_4131_, v___x_4110_, v___x_4132_);
                    if v_isShared_4096_ == 0 {
                        leanh::lean_ctor_set(v___x_4095_, 1, v___x_4133_);
                        v___x_4135_ = v___x_4095_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4136_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_size_4092_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 1, v___x_4133_);
                        v___x_4135_ = v_reuseFailAlloc_4136_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4125_;
            }
            4 => {
                return v___x_4128_;
            }
            5 => {
                return v___x_4135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(
    mut v_x_4140_: *mut leanh::LeanObject,
    mut v_x_4141_: *mut leanh::LeanObject,
    mut v_x_4142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stage_u2081_4143_: u8 = 0;
    let mut v_map_u2081_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4148_: u8 = 0;
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4153_: u8 = 0;
    let mut v_map_u2081_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4158_: u8 = 0;
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_4143_ = leanh::lean_ctor_get_uint8(
                    v_x_4140_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_4143_ == 0 {
                    v_map_u2081_4144_ = leanh::lean_ctor_get(v_x_4140_, 0);
                    v_map_u2082_4145_ = leanh::lean_ctor_get(v_x_4140_, 1);
                    v_isSharedCheck_4153_ = (!leanh::lean_is_exclusive(v_x_4140_)) as u8;
                    if v_isSharedCheck_4153_ == 0 {
                        v___x_4147_ = v_x_4140_;
                        v_isShared_4148_ = v_isSharedCheck_4153_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_map_u2082_4145_);
                        leanh::lean_inc(v_map_u2081_4144_);
                        leanh::lean_dec(v_x_4140_);
                        v___x_4147_ = leanh::lean_box(0);
                        v_isShared_4148_ = v_isSharedCheck_4153_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_map_u2081_4154_ = leanh::lean_ctor_get(v_x_4140_, 0);
                    v_map_u2082_4155_ = leanh::lean_ctor_get(v_x_4140_, 1);
                    v_isSharedCheck_4163_ = (!leanh::lean_is_exclusive(v_x_4140_)) as u8;
                    if v_isSharedCheck_4163_ == 0 {
                        v___x_4157_ = v_x_4140_;
                        v_isShared_4158_ = v_isSharedCheck_4163_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_map_u2082_4155_);
                        leanh::lean_inc(v_map_u2081_4154_);
                        leanh::lean_dec(v_x_4140_);
                        v___x_4157_ = leanh::lean_box(0);
                        v_isShared_4158_ = v_isSharedCheck_4163_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4149_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_map_u2082_4145_, v_x_4141_, v_x_4142_);
                if v_isShared_4148_ == 0 {
                    leanh::lean_ctor_set(v___x_4147_, 1, v___x_4149_);
                    v___x_4151_ = v___x_4147_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4152_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_map_u2081_4144_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4152_, 1, v___x_4149_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4152_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_stage_u2081_4143_,
                    );
                    v___x_4151_ = v_reuseFailAlloc_4152_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4151_;
            }
            3 => {
                v___x_4159_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_map_u2081_4154_, v_x_4141_, v_x_4142_);
                if v_isShared_4158_ == 0 {
                    leanh::lean_ctor_set(v___x_4157_, 0, v___x_4159_);
                    v___x_4161_ = v___x_4157_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4162_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4162_, 0, v___x_4159_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4162_, 1, v_map_u2082_4155_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4162_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_stage_u2081_4143_,
                    );
                    v___x_4161_ = v_reuseFailAlloc_4162_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4161_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(
    mut v_a_4164_: *mut leanh::LeanObject,
    mut v_x_4165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: u8 = 0;
    let mut v___x_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4165_) == 0 {
                    v___x_4166_ = leanh::lean_box(0);
                    return v___x_4166_;
                } else {
                    v_key_4167_ = leanh::lean_ctor_get(v_x_4165_, 0);
                    v_value_4168_ = leanh::lean_ctor_get(v_x_4165_, 1);
                    v_tail_4169_ = leanh::lean_ctor_get(v_x_4165_, 2);
                    v___x_4170_ = lean_name_eq(v_key_4167_, v_a_4164_);
                    if v___x_4170_ == 0 {
                        v_x_4165_ = v_tail_4169_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_4168_);
                        v___x_4172_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4172_, 0, v_value_4168_);
                        return v___x_4172_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_a_4173_: *mut leanh::LeanObject,
    mut v_x_4174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4175_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_4173_, v_x_4174_);
    leanh::lean_dec(v_x_4174_);
    leanh::lean_dec(v_a_4173_);
    return v_res_4175_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(
    mut v_m_4176_: *mut leanh::LeanObject,
    mut v_a_4177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4181_: u64 = 0;
    let mut v___x_4182_: u64 = 0;
    let mut v___x_4183_: u64 = 0;
    let mut v_fold_4184_: u64 = 0;
    let mut v___x_4185_: u64 = 0;
    let mut v___x_4186_: u64 = 0;
    let mut v___x_4187_: u64 = 0;
    let mut v___x_4188_: usize = 0;
    let mut v___x_4189_: usize = 0;
    let mut v___x_4190_: usize = 0;
    let mut v___x_4191_: usize = 0;
    let mut v___x_4192_: usize = 0;
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: u64 = 0;
    let mut v_hash_4196_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4178_ = leanh::lean_ctor_get(v_m_4176_, 1);
                v___x_4179_ = lean_array_get_size(v_buckets_4178_);
                if leanh::lean_obj_tag(v_a_4177_) == 0 {
                    v___x_4195_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
                    v___y_4181_ = v___x_4195_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4196_ = leanh::lean_ctor_get_uint64(
                        v_a_4177_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4181_ = v_hash_4196_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4182_ = 32u64;
                v___x_4183_ = lean_uint64_shift_right(v___y_4181_, v___x_4182_);
                v_fold_4184_ = lean_uint64_xor(v___y_4181_, v___x_4183_);
                v___x_4185_ = 16u64;
                v___x_4186_ = lean_uint64_shift_right(v_fold_4184_, v___x_4185_);
                v___x_4187_ = lean_uint64_xor(v_fold_4184_, v___x_4186_);
                v___x_4188_ = lean_uint64_to_usize(v___x_4187_);
                v___x_4189_ = lean_usize_of_nat(v___x_4179_);
                v___x_4190_ = 1usize;
                v___x_4191_ = lean_usize_sub(v___x_4189_, v___x_4190_);
                v___x_4192_ = lean_usize_land(v___x_4188_, v___x_4191_);
                v___x_4193_ = lean_array_uget_borrowed(v_buckets_4178_, v___x_4192_);
                v___x_4194_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_4177_, v___x_4193_);
                return v___x_4194_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg___boxed(
    mut v_m_4197_: *mut leanh::LeanObject,
    mut v_a_4198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4199_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_4197_, v_a_4198_);
    leanh::lean_dec(v_a_4198_);
    leanh::lean_dec_ref(v_m_4197_);
    return v_res_4199_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_keys_4200_: *mut leanh::LeanObject,
    mut v_vals_4201_: *mut leanh::LeanObject,
    mut v_i_4202_: *mut leanh::LeanObject,
    mut v_k_4203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: u8 = 0;
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: u8 = 0;
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4204_ = lean_array_get_size(v_keys_4200_);
                v___x_4205_ = lean_nat_dec_lt(v_i_4202_, v___x_4204_);
                if v___x_4205_ == 0 {
                    leanh::lean_dec(v_i_4202_);
                    v___x_4206_ = leanh::lean_box(0);
                    return v___x_4206_;
                } else {
                    v_k_x27_4207_ = lean_array_fget_borrowed(v_keys_4200_, v_i_4202_);
                    v___x_4208_ = lean_name_eq(v_k_4203_, v_k_x27_4207_);
                    if v___x_4208_ == 0 {
                        v___x_4209_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4210_ = lean_nat_add(v_i_4202_, v___x_4209_);
                        leanh::lean_dec(v_i_4202_);
                        v_i_4202_ = v___x_4210_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4212_ = lean_array_fget_borrowed(v_vals_4201_, v_i_4202_);
                        leanh::lean_dec(v_i_4202_);
                        leanh::lean_inc(v___x_4212_);
                        v___x_4213_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4213_, 0, v___x_4212_);
                        return v___x_4213_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_keys_4214_: *mut leanh::LeanObject,
    mut v_vals_4215_: *mut leanh::LeanObject,
    mut v_i_4216_: *mut leanh::LeanObject,
    mut v_k_4217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4218_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_4214_, v_vals_4215_, v_i_4216_, v_k_4217_);
    leanh::lean_dec(v_k_4217_);
    leanh::lean_dec_ref(v_vals_4215_);
    leanh::lean_dec_ref(v_keys_4214_);
    return v_res_4218_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(
    mut v_x_4219_: *mut leanh::LeanObject,
    mut v_x_4220_: usize,
    mut v_x_4221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: usize = 0;
    let mut v___x_4225_: usize = 0;
    let mut v___x_4226_: usize = 0;
    let mut v_j_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: u8 = 0;
    let mut v___x_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: usize = 0;
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4219_) == 0 {
                    v_es_4222_ = leanh::lean_ctor_get(v_x_4219_, 0);
                    v___x_4223_ = leanh::lean_box(2);
                    v___x_4224_ = 5usize;
                    v___x_4225_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__1);
                    v___x_4226_ = lean_usize_land(v_x_4220_, v___x_4225_);
                    v_j_4227_ = lean_usize_to_nat(v___x_4226_);
                    v___x_4228_ = lean_array_get_borrowed(v___x_4223_, v_es_4222_, v_j_4227_);
                    leanh::lean_dec(v_j_4227_);
                    match leanh::lean_obj_tag(v___x_4228_) {
                        0 => {
                            v_key_4229_ = leanh::lean_ctor_get(v___x_4228_, 0);
                            v_val_4230_ = leanh::lean_ctor_get(v___x_4228_, 1);
                            v___x_4231_ = lean_name_eq(v_x_4221_, v_key_4229_);
                            if v___x_4231_ == 0 {
                                v___x_4232_ = leanh::lean_box(0);
                                return v___x_4232_;
                            } else {
                                leanh::lean_inc(v_val_4230_);
                                v___x_4233_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4233_, 0, v_val_4230_);
                                return v___x_4233_;
                            }
                        }
                        1 => {
                            v_node_4234_ = leanh::lean_ctor_get(v___x_4228_, 0);
                            v___x_4235_ = lean_usize_shift_right(v_x_4220_, v___x_4224_);
                            v_x_4219_ = v_node_4234_;
                            v_x_4220_ = v___x_4235_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4237_ = leanh::lean_box(0);
                            return v___x_4237_;
                        }
                    }
                } else {
                    v_ks_4238_ = leanh::lean_ctor_get(v_x_4219_, 0);
                    v_vs_4239_ = leanh::lean_ctor_get(v_x_4219_, 1);
                    v___x_4240_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4241_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_4238_, v_vs_4239_, v___x_4240_, v_x_4221_);
                    return v___x_4241_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4242_: *mut leanh::LeanObject,
    mut v_x_4243_: *mut leanh::LeanObject,
    mut v_x_4244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1644__boxed_4245_: usize = 0;
    let mut v_res_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1644__boxed_4245_ = leanh::lean_unbox_usize(v_x_4243_);
    leanh::lean_dec(v_x_4243_);
    v_res_4246_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_4242_, v_x_1644__boxed_4245_, v_x_4244_);
    leanh::lean_dec(v_x_4244_);
    leanh::lean_dec_ref(v_x_4242_);
    return v_res_4246_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(
    mut v_x_4247_: *mut leanh::LeanObject,
    mut v_x_4248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4250_: u64 = 0;
    let mut v___x_4251_: usize = 0;
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: u64 = 0;
    let mut v_hash_4254_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4248_) == 0 {
                    v___x_4253_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
                    v___y_4250_ = v___x_4253_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4254_ = leanh::lean_ctor_get_uint64(
                        v_x_4248_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4250_ = v_hash_4254_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4251_ = lean_uint64_to_usize(v___y_4250_);
                v___x_4252_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_4247_, v___x_4251_, v_x_4248_);
                return v___x_4252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg___boxed(
    mut v_x_4255_: *mut leanh::LeanObject,
    mut v_x_4256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4257_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_4255_, v_x_4256_);
    leanh::lean_dec(v_x_4256_);
    leanh::lean_dec_ref(v_x_4255_);
    return v_res_4257_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(
    mut v_x_4258_: *mut leanh::LeanObject,
    mut v_x_4259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stage_u2081_4260_: u8 = 0;
    v_stage_u2081_4260_ = leanh::lean_ctor_get_uint8(
        v_x_4258_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_4260_ == 0 {
        let mut v_map_u2081_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_4261_ = leanh::lean_ctor_get(v_x_4258_, 0);
        v_map_u2082_4262_ = leanh::lean_ctor_get(v_x_4258_, 1);
        v___x_4263_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_map_u2082_4262_, v_x_4259_);
        if leanh::lean_obj_tag(v___x_4263_) == 0 {
            let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4264_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_4261_, v_x_4259_);
            return v___x_4264_;
        } else {
            return v___x_4263_;
        }
    } else {
        let mut v_map_u2081_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_4265_ = leanh::lean_ctor_get(v_x_4258_, 0);
        v___x_4266_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_4265_, v_x_4259_);
        return v___x_4266_;
    }
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg___boxed(
    mut v_x_4267_: *mut leanh::LeanObject,
    mut v_x_4268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4269_ =
        l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_4267_, v_x_4268_);
    leanh::lean_dec(v_x_4268_);
    leanh::lean_dec_ref(v_x_4267_);
    return v_res_4269_;
}
pub unsafe fn l_List_elem___at___00Lean_addAliasEntry_spec__2(
    mut v_a_4270_: *mut leanh::LeanObject,
    mut v_x_4271_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4272_: u8 = 0;
    let mut v_head_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4271_) == 0 {
                    v___x_4272_ = 0;
                    return v___x_4272_;
                } else {
                    v_head_4273_ = leanh::lean_ctor_get(v_x_4271_, 0);
                    v_tail_4274_ = leanh::lean_ctor_get(v_x_4271_, 1);
                    v___x_4275_ = lean_name_eq(v_a_4270_, v_head_4273_);
                    if v___x_4275_ == 0 {
                        v_x_4271_ = v_tail_4274_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4275_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lean_addAliasEntry_spec__2___boxed(
    mut v_a_4277_: *mut leanh::LeanObject,
    mut v_x_4278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4279_: u8 = 0;
    let mut v_r_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4279_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_a_4277_, v_x_4278_);
    leanh::lean_dec(v_x_4278_);
    leanh::lean_dec(v_a_4277_);
    v_r_4280_ = leanh::lean_box((v_res_4279_) as usize);
    return v_r_4280_;
}
pub unsafe fn l_Lean_addAliasEntry(
    mut v_s_4281_: *mut leanh::LeanObject,
    mut v_e_4282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4287_: u8 = 0;
    let mut v___x_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: u8 = 0;
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4283_ = leanh::lean_ctor_get(v_e_4282_, 0);
                v_snd_4284_ = leanh::lean_ctor_get(v_e_4282_, 1);
                v_isSharedCheck_4300_ = (!leanh::lean_is_exclusive(v_e_4282_)) as u8;
                if v_isSharedCheck_4300_ == 0 {
                    v___x_4286_ = v_e_4282_;
                    v_isShared_4287_ = v_isSharedCheck_4300_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4284_);
                    leanh::lean_inc(v_fst_4283_);
                    leanh::lean_dec(v_e_4282_);
                    v___x_4286_ = leanh::lean_box(0);
                    v_isShared_4287_ = v_isSharedCheck_4300_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4288_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(
                    v_s_4281_,
                    v_fst_4283_,
                );
                if leanh::lean_obj_tag(v___x_4288_) == 0 {
                    v___x_4289_ = leanh::lean_box(0);
                    if v_isShared_4287_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4286_, 1);
                        leanh::lean_ctor_set(v___x_4286_, 1, v___x_4289_);
                        leanh::lean_ctor_set(v___x_4286_, 0, v_snd_4284_);
                        v___x_4291_ = v___x_4286_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4293_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_snd_4284_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4293_, 1, v___x_4289_);
                        v___x_4291_ = v_reuseFailAlloc_4293_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_4294_ = leanh::lean_ctor_get(v___x_4288_, 0);
                    leanh::lean_inc(v_val_4294_);
                    leanh::lean_dec_ref_known(v___x_4288_, 1);
                    v___x_4295_ =
                        l_List_elem___at___00Lean_addAliasEntry_spec__2(v_snd_4284_, v_val_4294_);
                    if v___x_4295_ == 0 {
                        if v_isShared_4287_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_4286_, 1);
                            leanh::lean_ctor_set(v___x_4286_, 1, v_val_4294_);
                            leanh::lean_ctor_set(v___x_4286_, 0, v_snd_4284_);
                            v___x_4297_ = v___x_4286_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4299_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_snd_4284_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4299_, 1, v_val_4294_);
                            v___x_4297_ = v_reuseFailAlloc_4299_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_4294_);
                        leanh::lean_del_object(v___x_4286_);
                        leanh::lean_dec(v_snd_4284_);
                        leanh::lean_dec(v_fst_4283_);
                        return v_s_4281_;
                    }
                }
            }
            2 => {
                v___x_4292_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(
                    v_s_4281_,
                    v_fst_4283_,
                    v___x_4291_,
                );
                return v___x_4292_;
            }
            3 => {
                v___x_4298_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(
                    v_s_4281_,
                    v_fst_4283_,
                    v___x_4297_,
                );
                return v___x_4298_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(
    mut v_00_u03b2_4301_: *mut leanh::LeanObject,
    mut v_x_4302_: *mut leanh::LeanObject,
    mut v_x_4303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4304_ =
        l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_4302_, v_x_4303_);
    return v___x_4304_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___boxed(
    mut v_00_u03b2_4305_: *mut leanh::LeanObject,
    mut v_x_4306_: *mut leanh::LeanObject,
    mut v_x_4307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4308_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(
        v_00_u03b2_4305_,
        v_x_4306_,
        v_x_4307_,
    );
    leanh::lean_dec(v_x_4307_);
    leanh::lean_dec_ref(v_x_4306_);
    return v_res_4308_;
}
pub unsafe fn l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1(
    mut v_00_u03b2_4309_: *mut leanh::LeanObject,
    mut v_x_4310_: *mut leanh::LeanObject,
    mut v_x_4311_: *mut leanh::LeanObject,
    mut v_x_4312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4313_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(
        v_x_4310_, v_x_4311_, v_x_4312_,
    );
    return v___x_4313_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(
    mut v_00_u03b2_4314_: *mut leanh::LeanObject,
    mut v_x_4315_: *mut leanh::LeanObject,
    mut v_x_4316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4317_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_4315_, v_x_4316_);
    return v___x_4317_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___boxed(
    mut v_00_u03b2_4318_: *mut leanh::LeanObject,
    mut v_x_4319_: *mut leanh::LeanObject,
    mut v_x_4320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4321_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(v_00_u03b2_4318_, v_x_4319_, v_x_4320_);
    leanh::lean_dec(v_x_4320_);
    leanh::lean_dec_ref(v_x_4319_);
    return v_res_4321_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(
    mut v_00_u03b2_4322_: *mut leanh::LeanObject,
    mut v_m_4323_: *mut leanh::LeanObject,
    mut v_a_4324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4325_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_4323_, v_a_4324_);
    return v___x_4325_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___boxed(
    mut v_00_u03b2_4326_: *mut leanh::LeanObject,
    mut v_m_4327_: *mut leanh::LeanObject,
    mut v_a_4328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4329_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(v_00_u03b2_4326_, v_m_4327_, v_a_4328_);
    leanh::lean_dec(v_a_4328_);
    leanh::lean_dec_ref(v_m_4327_);
    return v_res_4329_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3(
    mut v_00_u03b2_4330_: *mut leanh::LeanObject,
    mut v_x_4331_: *mut leanh::LeanObject,
    mut v_x_4332_: *mut leanh::LeanObject,
    mut v_x_4333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4334_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_x_4331_, v_x_4332_, v_x_4333_);
    return v___x_4334_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4(
    mut v_00_u03b2_4335_: *mut leanh::LeanObject,
    mut v_m_4336_: *mut leanh::LeanObject,
    mut v_a_4337_: *mut leanh::LeanObject,
    mut v_b_4338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4339_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_m_4336_, v_a_4337_, v_b_4338_);
    return v___x_4339_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4340_: *mut leanh::LeanObject,
    mut v_x_4341_: *mut leanh::LeanObject,
    mut v_x_4342_: usize,
    mut v_x_4343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4344_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_4341_, v_x_4342_, v_x_4343_);
    return v___x_4344_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4345_: *mut leanh::LeanObject,
    mut v_x_4346_: *mut leanh::LeanObject,
    mut v_x_4347_: *mut leanh::LeanObject,
    mut v_x_4348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1814__boxed_4349_: usize = 0;
    let mut v_res_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1814__boxed_4349_ = leanh::lean_unbox_usize(v_x_4347_);
    leanh::lean_dec(v_x_4347_);
    v_res_4350_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(v_00_u03b2_4345_, v_x_4346_, v_x_1814__boxed_4349_, v_x_4348_);
    leanh::lean_dec(v_x_4348_);
    leanh::lean_dec_ref(v_x_4346_);
    return v_res_4350_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4351_: *mut leanh::LeanObject,
    mut v_a_4352_: *mut leanh::LeanObject,
    mut v_x_4353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4354_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_4352_, v_x_4353_);
    return v___x_4354_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4355_: *mut leanh::LeanObject,
    mut v_a_4356_: *mut leanh::LeanObject,
    mut v_x_4357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4358_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(v_00_u03b2_4355_, v_a_4356_, v_x_4357_);
    leanh::lean_dec(v_x_4357_);
    leanh::lean_dec(v_a_4356_);
    return v_res_4358_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(
    mut v_00_u03b2_4359_: *mut leanh::LeanObject,
    mut v_x_4360_: *mut leanh::LeanObject,
    mut v_x_4361_: usize,
    mut v_x_4362_: usize,
    mut v_x_4363_: *mut leanh::LeanObject,
    mut v_x_4364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4365_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_4360_, v_x_4361_, v_x_4362_, v_x_4363_, v_x_4364_);
    return v___x_4365_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___boxed(
    mut v_00_u03b2_4366_: *mut leanh::LeanObject,
    mut v_x_4367_: *mut leanh::LeanObject,
    mut v_x_4368_: *mut leanh::LeanObject,
    mut v_x_4369_: *mut leanh::LeanObject,
    mut v_x_4370_: *mut leanh::LeanObject,
    mut v_x_4371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1830__boxed_4372_: usize = 0;
    let mut v_x_1831__boxed_4373_: usize = 0;
    let mut v_res_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1830__boxed_4372_ = leanh::lean_unbox_usize(v_x_4368_);
    leanh::lean_dec(v_x_4368_);
    v_x_1831__boxed_4373_ = leanh::lean_unbox_usize(v_x_4369_);
    leanh::lean_dec(v_x_4369_);
    v_res_4374_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(v_00_u03b2_4366_, v_x_4367_, v_x_1830__boxed_4372_, v_x_1831__boxed_4373_, v_x_4370_, v_x_4371_);
    return v_res_4374_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(
    mut v_00_u03b2_4375_: *mut leanh::LeanObject,
    mut v_a_4376_: *mut leanh::LeanObject,
    mut v_x_4377_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4378_: u8 = 0;
    v___x_4378_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_4376_, v_x_4377_);
    return v___x_4378_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___boxed(
    mut v_00_u03b2_4379_: *mut leanh::LeanObject,
    mut v_a_4380_: *mut leanh::LeanObject,
    mut v_x_4381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4382_: u8 = 0;
    let mut v_r_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4382_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(v_00_u03b2_4379_, v_a_4380_, v_x_4381_);
    leanh::lean_dec(v_x_4381_);
    leanh::lean_dec(v_a_4380_);
    v_r_4383_ = leanh::lean_box((v_res_4382_) as usize);
    return v_r_4383_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9(
    mut v_00_u03b2_4384_: *mut leanh::LeanObject,
    mut v_data_4385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4386_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_data_4385_);
    return v___x_4386_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10(
    mut v_00_u03b2_4387_: *mut leanh::LeanObject,
    mut v_a_4388_: *mut leanh::LeanObject,
    mut v_b_4389_: *mut leanh::LeanObject,
    mut v_x_4390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4391_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_4388_, v_b_4389_, v_x_4390_);
    return v___x_4391_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b2_4392_: *mut leanh::LeanObject,
    mut v_keys_4393_: *mut leanh::LeanObject,
    mut v_vals_4394_: *mut leanh::LeanObject,
    mut v_heq_4395_: *mut leanh::LeanObject,
    mut v_i_4396_: *mut leanh::LeanObject,
    mut v_k_4397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4398_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_4393_, v_vals_4394_, v_i_4396_, v_k_4397_);
    return v___x_4398_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b2_4399_: *mut leanh::LeanObject,
    mut v_keys_4400_: *mut leanh::LeanObject,
    mut v_vals_4401_: *mut leanh::LeanObject,
    mut v_heq_4402_: *mut leanh::LeanObject,
    mut v_i_4403_: *mut leanh::LeanObject,
    mut v_k_4404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4405_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_4399_, v_keys_4400_, v_vals_4401_, v_heq_4402_, v_i_4403_, v_k_4404_);
    leanh::lean_dec(v_k_4404_);
    leanh::lean_dec_ref(v_vals_4401_);
    leanh::lean_dec_ref(v_keys_4400_);
    return v_res_4405_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9(
    mut v_00_u03b2_4406_: *mut leanh::LeanObject,
    mut v_n_4407_: *mut leanh::LeanObject,
    mut v_k_4408_: *mut leanh::LeanObject,
    mut v_v_4409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4410_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v_n_4407_, v_k_4408_, v_v_4409_);
    return v___x_4410_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(
    mut v_00_u03b2_4411_: *mut leanh::LeanObject,
    mut v_depth_4412_: usize,
    mut v_keys_4413_: *mut leanh::LeanObject,
    mut v_vals_4414_: *mut leanh::LeanObject,
    mut v_heq_4415_: *mut leanh::LeanObject,
    mut v_i_4416_: *mut leanh::LeanObject,
    mut v_entries_4417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4418_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_4412_, v_keys_4413_, v_vals_4414_, v_i_4416_, v_entries_4417_);
    return v___x_4418_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___boxed(
    mut v_00_u03b2_4419_: *mut leanh::LeanObject,
    mut v_depth_4420_: *mut leanh::LeanObject,
    mut v_keys_4421_: *mut leanh::LeanObject,
    mut v_vals_4422_: *mut leanh::LeanObject,
    mut v_heq_4423_: *mut leanh::LeanObject,
    mut v_i_4424_: *mut leanh::LeanObject,
    mut v_entries_4425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4426_: usize = 0;
    let mut v_res_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4426_ = leanh::lean_unbox_usize(v_depth_4420_);
    leanh::lean_dec(v_depth_4420_);
    v_res_4427_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_4419_, v_depth_boxed_4426_, v_keys_4421_, v_vals_4422_, v_heq_4423_, v_i_4424_, v_entries_4425_);
    leanh::lean_dec_ref(v_vals_4422_);
    leanh::lean_dec_ref(v_keys_4421_);
    return v_res_4427_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14(
    mut v_00_u03b2_4428_: *mut leanh::LeanObject,
    mut v_i_4429_: *mut leanh::LeanObject,
    mut v_source_4430_: *mut leanh::LeanObject,
    mut v_target_4431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4432_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v_i_4429_, v_source_4430_, v_target_4431_);
    return v___x_4432_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11(
    mut v_00_u03b2_4433_: *mut leanh::LeanObject,
    mut v_x_4434_: *mut leanh::LeanObject,
    mut v_x_4435_: *mut leanh::LeanObject,
    mut v_x_4436_: *mut leanh::LeanObject,
    mut v_x_4437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4438_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_x_4434_, v_x_4435_, v_x_4436_, v_x_4437_);
    return v___x_4438_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16(
    mut v_00_u03b2_4439_: *mut leanh::LeanObject,
    mut v_x_4440_: *mut leanh::LeanObject,
    mut v_x_4441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4442_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_x_4440_, v_x_4441_);
    return v___x_4442_;
}
pub unsafe fn l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(
    mut v_m_4443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stage_u2081_4444_: u8 = 0;
    let mut v_map_u2081_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4449_: u8 = 0;
    let mut v___x_4450_: u8 = 0;
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4454_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_4444_ = leanh::lean_ctor_get_uint8(
                    v_m_4443_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_4444_ == 0 {
                    return v_m_4443_;
                } else {
                    v_map_u2081_4445_ = leanh::lean_ctor_get(v_m_4443_, 0);
                    v_map_u2082_4446_ = leanh::lean_ctor_get(v_m_4443_, 1);
                    v_isSharedCheck_4454_ = (!leanh::lean_is_exclusive(v_m_4443_)) as u8;
                    if v_isSharedCheck_4454_ == 0 {
                        v___x_4448_ = v_m_4443_;
                        v_isShared_4449_ = v_isSharedCheck_4454_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_map_u2082_4446_);
                        leanh::lean_inc(v_map_u2081_4445_);
                        leanh::lean_dec(v_m_4443_);
                        v___x_4448_ = leanh::lean_box(0);
                        v_isShared_4449_ = v_isSharedCheck_4454_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4450_ = 0;
                if v_isShared_4449_ == 0 {
                    v___x_4452_ = v___x_4448_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4453_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_map_u2081_4445_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4453_, 1, v_map_u2082_4446_);
                    v___x_4452_ = v_reuseFailAlloc_4453_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_4452_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_4450_,
                );
                return v___x_4452_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1(
    mut v_00_u03b2_4455_: *mut leanh::LeanObject,
    mut v_m_4456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4457_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v_m_4456_);
    return v___x_4457_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(
    mut v_es_4458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4459_ = lean_array_mk(v_es_4458_);
    return v___x_4459_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(
    mut v_as_4460_: *mut leanh::LeanObject,
    mut v_i_4461_: usize,
    mut v_stop_4462_: usize,
    mut v_b_4463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4464_: u8 = 0;
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: usize = 0;
    let mut v___x_4468_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4464_ = lean_usize_dec_eq(v_i_4461_, v_stop_4462_);
                if v___x_4464_ == 0 {
                    v___x_4465_ = lean_array_uget_borrowed(v_as_4460_, v_i_4461_);
                    leanh::lean_inc(v___x_4465_);
                    v___x_4466_ = l_Lean_addAliasEntry(v_b_4463_, v___x_4465_);
                    v___x_4467_ = 1usize;
                    v___x_4468_ = lean_usize_add(v_i_4461_, v___x_4467_);
                    v_i_4461_ = v___x_4468_;
                    v_b_4463_ = v___x_4466_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4463_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_as_4470_: *mut leanh::LeanObject,
    mut v_i_4471_: *mut leanh::LeanObject,
    mut v_stop_4472_: *mut leanh::LeanObject,
    mut v_b_4473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4474_: usize = 0;
    let mut v_stop_boxed_4475_: usize = 0;
    let mut v_res_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4474_ = leanh::lean_unbox_usize(v_i_4471_);
    leanh::lean_dec(v_i_4471_);
    v_stop_boxed_4475_ = leanh::lean_unbox_usize(v_stop_4472_);
    leanh::lean_dec(v_stop_4472_);
    v_res_4476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v_as_4470_, v_i_boxed_4474_, v_stop_boxed_4475_, v_b_4473_);
    leanh::lean_dec_ref(v_as_4470_);
    return v_res_4476_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(
    mut v_as_4477_: *mut leanh::LeanObject,
    mut v_i_4478_: usize,
    mut v_stop_4479_: usize,
    mut v_b_4480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: usize = 0;
    let mut v___x_4484_: usize = 0;
    let mut v___x_4486_: u8 = 0;
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: u8 = 0;
    let mut v___x_4491_: u8 = 0;
    let mut v___x_4492_: usize = 0;
    let mut v___x_4493_: usize = 0;
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: usize = 0;
    let mut v___x_4496_: usize = 0;
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4486_ = lean_usize_dec_eq(v_i_4478_, v_stop_4479_);
                if v___x_4486_ == 0 {
                    v___x_4487_ = lean_array_uget_borrowed(v_as_4477_, v_i_4478_);
                    v___x_4488_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4489_ = lean_array_get_size(v___x_4487_);
                    v___x_4490_ = lean_nat_dec_lt(v___x_4488_, v___x_4489_);
                    if v___x_4490_ == 0 {
                        v___y_4482_ = v_b_4480_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4491_ = lean_nat_dec_le(v___x_4489_, v___x_4489_);
                        if v___x_4491_ == 0 {
                            if v___x_4490_ == 0 {
                                v___y_4482_ = v_b_4480_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4492_ = 0usize;
                                v___x_4493_ = lean_usize_of_nat(v___x_4489_);
                                v___x_4494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v___x_4487_, v___x_4492_, v___x_4493_, v_b_4480_);
                                v___y_4482_ = v___x_4494_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_4495_ = 0usize;
                            v___x_4496_ = lean_usize_of_nat(v___x_4489_);
                            v___x_4497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v___x_4487_, v___x_4495_, v___x_4496_, v_b_4480_);
                            v___y_4482_ = v___x_4497_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_4480_;
                }
            }
            1 => {
                v___x_4483_ = 1usize;
                v___x_4484_ = lean_usize_add(v_i_4478_, v___x_4483_);
                v_i_4478_ = v___x_4484_;
                v_b_4480_ = v___y_4482_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1___boxed(
    mut v_as_4498_: *mut leanh::LeanObject,
    mut v_i_4499_: *mut leanh::LeanObject,
    mut v_stop_4500_: *mut leanh::LeanObject,
    mut v_b_4501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4502_: usize = 0;
    let mut v_stop_boxed_4503_: usize = 0;
    let mut v_res_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4502_ = leanh::lean_unbox_usize(v_i_4499_);
    leanh::lean_dec(v_i_4499_);
    v_stop_boxed_4503_ = leanh::lean_unbox_usize(v_stop_4500_);
    leanh::lean_dec(v_stop_4500_);
    v_res_4504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_4498_, v_i_boxed_4502_, v_stop_boxed_4503_, v_b_4501_);
    leanh::lean_dec_ref(v_as_4498_);
    return v_res_4504_;
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(
    mut v_initState_4505_: *mut leanh::LeanObject,
    mut v_as_4506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: u8 = 0;
    v___x_4507_ = leanh::lean_unsigned_to_nat(0);
    v___x_4508_ = lean_array_get_size(v_as_4506_);
    v___x_4509_ = lean_nat_dec_lt(v___x_4507_, v___x_4508_);
    if v___x_4509_ == 0 {
        return v_initState_4505_;
    } else {
        let mut v___x_4510_: u8 = 0;
        v___x_4510_ = lean_nat_dec_le(v___x_4508_, v___x_4508_);
        if v___x_4510_ == 0 {
            if v___x_4509_ == 0 {
                return v_initState_4505_;
            } else {
                let mut v___x_4511_: usize = 0;
                let mut v___x_4512_: usize = 0;
                let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4511_ = 0usize;
                v___x_4512_ = lean_usize_of_nat(v___x_4508_);
                v___x_4513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_4506_, v___x_4511_, v___x_4512_, v_initState_4505_);
                return v___x_4513_;
            }
        } else {
            let mut v___x_4514_: usize = 0;
            let mut v___x_4515_: usize = 0;
            let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4514_ = 0usize;
            v___x_4515_ = lean_usize_of_nat(v___x_4508_);
            v___x_4516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_4506_, v___x_4514_, v___x_4515_, v_initState_4505_);
            return v___x_4516_;
        }
    }
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0___boxed(
    mut v_initState_4517_: *mut leanh::LeanObject,
    mut v_as_4518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4519_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v_initState_4517_, v_as_4518_);
    leanh::lean_dec_ref(v_as_4518_);
    return v_res_4519_;
}
pub unsafe fn _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4520_ = leanh::lean_box(0);
    v___x_4521_ = leanh::lean_unsigned_to_nat(16);
    v___x_4522_ = lean_mk_array(v___x_4521_, v___x_4520_);
    return v___x_4522_;
}
pub unsafe fn _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4523_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once), _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
    v___x_4524_ = leanh::lean_unsigned_to_nat(0);
    v___x_4525_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4525_, 0, v___x_4524_);
    leanh::lean_ctor_set(v___x_4525_, 1, v___x_4523_);
    return v___x_4525_;
}
pub unsafe fn _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4526_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4526_;
}
pub unsafe fn _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4527_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once), _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
    v___x_4528_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4528_, 0, v___x_4527_);
    return v___x_4528_;
}
pub unsafe fn _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: u8 = 0;
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4529_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once), _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
    v___x_4530_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once), _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
    v___x_4531_ = 1;
    v___x_4532_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
    leanh::lean_ctor_set(v___x_4532_, 0, v___x_4530_);
    leanh::lean_ctor_set(v___x_4532_, 1, v___x_4529_);
    leanh::lean_ctor_set_uint8(
        v___x_4532_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_4531_,
    );
    return v___x_4532_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(
    mut v_es_4533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4534_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once), _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
    v___x_4535_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v___x_4534_, v_es_4533_);
    v___x_4536_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v___x_4535_);
    return v___x_4536_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(
    mut v_es_4537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4538_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(v_es_4537_);
    leanh::lean_dec_ref(v_es_4537_);
    return v_res_4538_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4555_ = l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
    v___x_4556_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_4555_);
    return v___x_4556_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(
    mut v_a_4557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4558_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
    return v_res_4558_;
}
pub unsafe fn lean_add_alias(
    mut v_env_4559_: *mut leanh::LeanObject,
    mut v_a_4560_: *mut leanh::LeanObject,
    mut v_e_4561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4562_ = l_Lean_aliasExtension;
    v_toEnvExtension_4563_ = leanh::lean_ctor_get(v___x_4562_, 0);
    v_asyncMode_4564_ = leanh::lean_ctor_get(v_toEnvExtension_4563_, 2);
    v___x_4565_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4565_, 0, v_a_4560_);
    leanh::lean_ctor_set(v___x_4565_, 1, v_e_4561_);
    v___x_4566_ = leanh::lean_box(0);
    v___x_4567_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
        v___x_4562_,
        v_env_4559_,
        v___x_4565_,
        v_asyncMode_4564_,
        v___x_4566_,
    );
    return v___x_4567_;
}
pub unsafe fn _init_l_Lean_getAliasState___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4570_ = l_Lean_getAliasState___closed__1;
    v___x_4571_ = l_Lean_getAliasState___closed__0;
    v___x_4572_ = l_Lean_SMap_instInhabited(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4571_,
        v___x_4570_,
    );
    return v___x_4572_;
}
pub unsafe fn l_Lean_getAliasState(
    mut v_env_4573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4574_ = l_Lean_aliasExtension;
    v_toEnvExtension_4575_ = leanh::lean_ctor_get(v___x_4574_, 0);
    v_asyncMode_4576_ = leanh::lean_ctor_get(v_toEnvExtension_4575_, 2);
    v___x_4577_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_getAliasState___closed__2),
        core::ptr::addr_of_mut!(l_Lean_getAliasState___closed__2_once),
        _init_l_Lean_getAliasState___closed__2,
    );
    v___x_4578_ = leanh::lean_box(0);
    v___x_4579_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_4577_,
        v___x_4574_,
        v_env_4573_,
        v_asyncMode_4576_,
        v___x_4578_,
    );
    return v___x_4579_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_getAliases_spec__0(
    mut v_env_4580_: *mut leanh::LeanObject,
    mut v_skipProtected_4581_: u8,
    mut v_a_4582_: *mut leanh::LeanObject,
    mut v_a_4583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4589_: u8 = 0;
    let mut v___x_4590_: u8 = 0;
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4582_) == 0 {
                    leanh::lean_dec_ref(v_env_4580_);
                    v___x_4584_ = l_List_reverse___redArg(v_a_4583_);
                    return v___x_4584_;
                } else {
                    v_head_4585_ = leanh::lean_ctor_get(v_a_4582_, 0);
                    v_tail_4586_ = leanh::lean_ctor_get(v_a_4582_, 1);
                    v_isSharedCheck_4597_ = (!leanh::lean_is_exclusive(v_a_4582_)) as u8;
                    if v_isSharedCheck_4597_ == 0 {
                        v___x_4588_ = v_a_4582_;
                        v_isShared_4589_ = v_isSharedCheck_4597_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4586_);
                        leanh::lean_inc(v_head_4585_);
                        leanh::lean_dec(v_a_4582_);
                        v___x_4588_ = leanh::lean_box(0);
                        v_isShared_4589_ = v_isSharedCheck_4597_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_head_4585_);
                leanh::lean_inc_ref(v_env_4580_);
                v___x_4590_ = l_Lean_isProtected(v_env_4580_, v_head_4585_);
                if v___x_4590_ == 0 {
                    if v_skipProtected_4581_ == 0 {
                        leanh::lean_del_object(v___x_4588_);
                        leanh::lean_dec(v_head_4585_);
                        v_a_4582_ = v_tail_4586_;
                        state = 0;
                        continue;
                    } else {
                        if v_isShared_4589_ == 0 {
                            leanh::lean_ctor_set(v___x_4588_, 1, v_a_4583_);
                            v___x_4593_ = v___x_4588_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4595_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4595_, 0, v_head_4585_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4595_, 1, v_a_4583_);
                            v___x_4593_ = v_reuseFailAlloc_4595_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4588_);
                    leanh::lean_dec(v_head_4585_);
                    v_a_4582_ = v_tail_4586_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_a_4582_ = v_tail_4586_;
                v_a_4583_ = v___x_4593_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_getAliases_spec__0___boxed(
    mut v_env_4598_: *mut leanh::LeanObject,
    mut v_skipProtected_4599_: *mut leanh::LeanObject,
    mut v_a_4600_: *mut leanh::LeanObject,
    mut v_a_4601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipProtected_boxed_4602_: u8 = 0;
    let mut v_res_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipProtected_boxed_4602_ = (leanh::lean_unbox(v_skipProtected_4599_) as u8);
    v_res_4603_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(
        v_env_4598_,
        v_skipProtected_boxed_4602_,
        v_a_4600_,
        v_a_4601_,
    );
    return v_res_4603_;
}
pub unsafe fn l_Lean_getAliases(
    mut v_env_4604_: *mut leanh::LeanObject,
    mut v_a_4605_: *mut leanh::LeanObject,
    mut v_skipProtected_4606_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4607_ = l_Lean_aliasExtension;
    v_toEnvExtension_4608_ = leanh::lean_ctor_get(v___x_4607_, 0);
    v_asyncMode_4609_ = leanh::lean_ctor_get(v_toEnvExtension_4608_, 2);
    v___x_4610_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_getAliasState___closed__2),
        core::ptr::addr_of_mut!(l_Lean_getAliasState___closed__2_once),
        _init_l_Lean_getAliasState___closed__2,
    );
    v___x_4611_ = leanh::lean_box(0);
    leanh::lean_inc_ref(v_env_4604_);
    v___x_4612_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_4610_,
        v___x_4607_,
        v_env_4604_,
        v_asyncMode_4609_,
        v___x_4611_,
    );
    v___x_4613_ =
        l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v___x_4612_, v_a_4605_);
    leanh::lean_dec(v___x_4612_);
    if leanh::lean_obj_tag(v___x_4613_) == 0 {
        let mut v___x_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_env_4604_);
        v___x_4614_ = leanh::lean_box(0);
        return v___x_4614_;
    } else {
        if v_skipProtected_4606_ == 0 {
            let mut v_val_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_env_4604_);
            v_val_4615_ = leanh::lean_ctor_get(v___x_4613_, 0);
            leanh::lean_inc(v_val_4615_);
            leanh::lean_dec_ref_known(v___x_4613_, 1);
            return v_val_4615_;
        } else {
            let mut v_val_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_4616_ = leanh::lean_ctor_get(v___x_4613_, 0);
            leanh::lean_inc(v_val_4616_);
            leanh::lean_dec_ref_known(v___x_4613_, 1);
            v___x_4617_ = leanh::lean_box(0);
            v___x_4618_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(
                v_env_4604_,
                v_skipProtected_4606_,
                v_val_4616_,
                v___x_4617_,
            );
            return v___x_4618_;
        }
    }
}
pub unsafe fn l_Lean_getAliases___boxed(
    mut v_env_4619_: *mut leanh::LeanObject,
    mut v_a_4620_: *mut leanh::LeanObject,
    mut v_skipProtected_4621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipProtected_boxed_4622_: u8 = 0;
    let mut v_res_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipProtected_boxed_4622_ = (leanh::lean_unbox(v_skipProtected_4621_) as u8);
    v_res_4623_ = l_Lean_getAliases(v_env_4619_, v_a_4620_, v_skipProtected_boxed_4622_);
    leanh::lean_dec(v_a_4620_);
    return v_res_4623_;
}
pub unsafe fn l_Lean_getRevAliases___lam__0(
    mut v_e_4624_: *mut leanh::LeanObject,
    mut v_as_4625_: *mut leanh::LeanObject,
    mut v_a_4626_: *mut leanh::LeanObject,
    mut v_es_4627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4628_: u8 = 0;
    v___x_4628_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_e_4624_, v_es_4627_);
    if v___x_4628_ == 0 {
        leanh::lean_dec(v_a_4626_);
        return v_as_4625_;
    } else {
        let mut v___x_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4629_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4629_, 0, v_a_4626_);
        leanh::lean_ctor_set(v___x_4629_, 1, v_as_4625_);
        return v___x_4629_;
    }
}
pub unsafe fn l_Lean_getRevAliases___lam__0___boxed(
    mut v_e_4630_: *mut leanh::LeanObject,
    mut v_as_4631_: *mut leanh::LeanObject,
    mut v_a_4632_: *mut leanh::LeanObject,
    mut v_es_4633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4634_ = l_Lean_getRevAliases___lam__0(v_e_4630_, v_as_4631_, v_a_4632_, v_es_4633_);
    leanh::lean_dec(v_es_4633_);
    leanh::lean_dec(v_e_4630_);
    return v_res_4634_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(
    mut v_f_4635_: *mut leanh::LeanObject,
    mut v_keys_4636_: *mut leanh::LeanObject,
    mut v_vals_4637_: *mut leanh::LeanObject,
    mut v_i_4638_: *mut leanh::LeanObject,
    mut v_acc_4639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: u8 = 0;
    let mut v_k_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4640_ = lean_array_get_size(v_keys_4636_);
                v___x_4641_ = lean_nat_dec_lt(v_i_4638_, v___x_4640_);
                if v___x_4641_ == 0 {
                    leanh::lean_dec(v_i_4638_);
                    leanh::lean_dec(v_f_4635_);
                    return v_acc_4639_;
                } else {
                    v_k_4642_ = lean_array_fget_borrowed(v_keys_4636_, v_i_4638_);
                    v_v_4643_ = lean_array_fget_borrowed(v_vals_4637_, v_i_4638_);
                    leanh::lean_inc(v_f_4635_);
                    leanh::lean_inc(v_v_4643_);
                    leanh::lean_inc(v_k_4642_);
                    v___x_4644_ =
                        leanh::lean_apply_3(v_f_4635_, v_acc_4639_, v_k_4642_, v_v_4643_);
                    v___x_4645_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4646_ = lean_nat_add(v_i_4638_, v___x_4645_);
                    leanh::lean_dec(v_i_4638_);
                    v_i_4638_ = v___x_4646_;
                    v_acc_4639_ = v___x_4644_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg___boxed(
    mut v_f_4648_: *mut leanh::LeanObject,
    mut v_keys_4649_: *mut leanh::LeanObject,
    mut v_vals_4650_: *mut leanh::LeanObject,
    mut v_i_4651_: *mut leanh::LeanObject,
    mut v_acc_4652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4653_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_4648_, v_keys_4649_, v_vals_4650_, v_i_4651_, v_acc_4652_);
    leanh::lean_dec_ref(v_vals_4650_);
    leanh::lean_dec_ref(v_keys_4649_);
    return v_res_4653_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_f_4654_: *mut leanh::LeanObject,
    mut v_x_4655_: *mut leanh::LeanObject,
    mut v_x_4656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4655_) == 0 {
        let mut v_es_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4660_: u8 = 0;
        v_es_4657_ = leanh::lean_ctor_get(v_x_4655_, 0);
        v___x_4658_ = leanh::lean_unsigned_to_nat(0);
        v___x_4659_ = lean_array_get_size(v_es_4657_);
        v___x_4660_ = lean_nat_dec_lt(v___x_4658_, v___x_4659_);
        if v___x_4660_ == 0 {
            leanh::lean_dec(v_f_4654_);
            return v_x_4656_;
        } else {
            let mut v___x_4661_: u8 = 0;
            v___x_4661_ = lean_nat_dec_le(v___x_4659_, v___x_4659_);
            if v___x_4661_ == 0 {
                if v___x_4660_ == 0 {
                    leanh::lean_dec(v_f_4654_);
                    return v_x_4656_;
                } else {
                    let mut v___x_4662_: usize = 0;
                    let mut v___x_4663_: usize = 0;
                    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_4662_ = 0usize;
                    v___x_4663_ = lean_usize_of_nat(v___x_4659_);
                    v___x_4664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_4654_, v_es_4657_, v___x_4662_, v___x_4663_, v_x_4656_);
                    return v___x_4664_;
                }
            } else {
                let mut v___x_4665_: usize = 0;
                let mut v___x_4666_: usize = 0;
                let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4665_ = 0usize;
                v___x_4666_ = lean_usize_of_nat(v___x_4659_);
                v___x_4667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_4654_, v_es_4657_, v___x_4665_, v___x_4666_, v_x_4656_);
                return v___x_4667_;
            }
        }
    } else {
        let mut v_ks_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ks_4668_ = leanh::lean_ctor_get(v_x_4655_, 0);
        v_vs_4669_ = leanh::lean_ctor_get(v_x_4655_, 1);
        v___x_4670_ = leanh::lean_unsigned_to_nat(0);
        v___x_4671_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_4654_, v_ks_4668_, v_vs_4669_, v___x_4670_, v_x_4656_);
        return v___x_4671_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(
    mut v_f_4672_: *mut leanh::LeanObject,
    mut v_as_4673_: *mut leanh::LeanObject,
    mut v_i_4674_: usize,
    mut v_stop_4675_: usize,
    mut v_b_4676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: usize = 0;
    let mut v___x_4680_: usize = 0;
    let mut v___x_4682_: u8 = 0;
    let mut v___x_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4682_ = lean_usize_dec_eq(v_i_4674_, v_stop_4675_);
                if v___x_4682_ == 0 {
                    v___x_4683_ = lean_array_uget_borrowed(v_as_4673_, v_i_4674_);
                    match leanh::lean_obj_tag(v___x_4683_) {
                        0 => {
                            v_key_4684_ = leanh::lean_ctor_get(v___x_4683_, 0);
                            v_val_4685_ = leanh::lean_ctor_get(v___x_4683_, 1);
                            leanh::lean_inc(v_f_4672_);
                            leanh::lean_inc(v_val_4685_);
                            leanh::lean_inc(v_key_4684_);
                            v___x_4686_ = leanh::lean_apply_3(
                                v_f_4672_,
                                v_b_4676_,
                                v_key_4684_,
                                v_val_4685_,
                            );
                            v___y_4678_ = v___x_4686_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_4687_ = leanh::lean_ctor_get(v___x_4683_, 0);
                            leanh::lean_inc(v_f_4672_);
                            v___x_4688_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_4672_, v_node_4687_, v_b_4676_);
                            v___y_4678_ = v___x_4688_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_4678_ = v_b_4676_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_f_4672_);
                    return v_b_4676_;
                }
            }
            1 => {
                v___x_4679_ = 1usize;
                v___x_4680_ = lean_usize_add(v_i_4674_, v___x_4679_);
                v_i_4674_ = v___x_4680_;
                v_b_4676_ = v___y_4678_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(
    mut v_f_4689_: *mut leanh::LeanObject,
    mut v_as_4690_: *mut leanh::LeanObject,
    mut v_i_4691_: *mut leanh::LeanObject,
    mut v_stop_4692_: *mut leanh::LeanObject,
    mut v_b_4693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4694_: usize = 0;
    let mut v_stop_boxed_4695_: usize = 0;
    let mut v_res_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4694_ = leanh::lean_unbox_usize(v_i_4691_);
    leanh::lean_dec(v_i_4691_);
    v_stop_boxed_4695_ = leanh::lean_unbox_usize(v_stop_4692_);
    leanh::lean_dec(v_stop_4692_);
    v_res_4696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_4689_, v_as_4690_, v_i_boxed_4694_, v_stop_boxed_4695_, v_b_4693_);
    leanh::lean_dec_ref(v_as_4690_);
    return v_res_4696_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_f_4697_: *mut leanh::LeanObject,
    mut v_x_4698_: *mut leanh::LeanObject,
    mut v_x_4699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4700_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_4697_, v_x_4698_, v_x_4699_);
    leanh::lean_dec_ref(v_x_4698_);
    return v_res_4700_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0(
    mut v_f_4701_: *mut leanh::LeanObject,
    mut v_x1_4702_: *mut leanh::LeanObject,
    mut v_x2_4703_: *mut leanh::LeanObject,
    mut v_x3_4704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4705_ = leanh::lean_apply_3(v_f_4701_, v_x1_4702_, v_x2_4703_, v_x3_4704_);
    return v___x_4705_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(
    mut v_map_4706_: *mut leanh::LeanObject,
    mut v_f_4707_: *mut leanh::LeanObject,
    mut v_init_4708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4709_ = leanh::lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    leanh::lean_closure_set(v___f_4709_, 0, v_f_4707_);
    v___x_4710_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v___f_4709_, v_map_4706_, v_init_4708_);
    return v___x_4710_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___boxed(
    mut v_map_4711_: *mut leanh::LeanObject,
    mut v_f_4712_: *mut leanh::LeanObject,
    mut v_init_4713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4714_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_4711_, v_f_4712_, v_init_4713_);
    leanh::lean_dec_ref(v_map_4711_);
    return v_res_4714_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(
    mut v_f_4715_: *mut leanh::LeanObject,
    mut v_x_4716_: *mut leanh::LeanObject,
    mut v_x_4717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4717_) == 0 {
                    leanh::lean_dec(v_f_4715_);
                    return v_x_4716_;
                } else {
                    v_key_4718_ = leanh::lean_ctor_get(v_x_4717_, 0);
                    leanh::lean_inc(v_key_4718_);
                    v_value_4719_ = leanh::lean_ctor_get(v_x_4717_, 1);
                    leanh::lean_inc(v_value_4719_);
                    v_tail_4720_ = leanh::lean_ctor_get(v_x_4717_, 2);
                    leanh::lean_inc(v_tail_4720_);
                    leanh::lean_dec_ref_known(v_x_4717_, 3);
                    leanh::lean_inc(v_f_4715_);
                    v___x_4721_ = leanh::lean_apply_3(
                        v_f_4715_,
                        v_x_4716_,
                        v_key_4718_,
                        v_value_4719_,
                    );
                    v_x_4716_ = v___x_4721_;
                    v_x_4717_ = v_tail_4720_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(
    mut v_f_4723_: *mut leanh::LeanObject,
    mut v_as_4724_: *mut leanh::LeanObject,
    mut v_i_4725_: usize,
    mut v_stop_4726_: usize,
    mut v_b_4727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4728_: u8 = 0;
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: usize = 0;
    let mut v___x_4732_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4728_ = lean_usize_dec_eq(v_i_4725_, v_stop_4726_);
                if v___x_4728_ == 0 {
                    v___x_4729_ = lean_array_uget_borrowed(v_as_4724_, v_i_4725_);
                    leanh::lean_inc(v___x_4729_);
                    leanh::lean_inc(v_f_4723_);
                    v___x_4730_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_4723_, v_b_4727_, v___x_4729_);
                    v___x_4731_ = 1usize;
                    v___x_4732_ = lean_usize_add(v_i_4725_, v___x_4731_);
                    v_i_4725_ = v___x_4732_;
                    v_b_4727_ = v___x_4730_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_f_4723_);
                    return v_b_4727_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg___boxed(
    mut v_f_4734_: *mut leanh::LeanObject,
    mut v_as_4735_: *mut leanh::LeanObject,
    mut v_i_4736_: *mut leanh::LeanObject,
    mut v_stop_4737_: *mut leanh::LeanObject,
    mut v_b_4738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4739_: usize = 0;
    let mut v_stop_boxed_4740_: usize = 0;
    let mut v_res_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4739_ = leanh::lean_unbox_usize(v_i_4736_);
    leanh::lean_dec(v_i_4736_);
    v_stop_boxed_4740_ = leanh::lean_unbox_usize(v_stop_4737_);
    leanh::lean_dec(v_stop_4737_);
    v_res_4741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_4734_, v_as_4735_, v_i_boxed_4739_, v_stop_boxed_4740_, v_b_4738_);
    leanh::lean_dec_ref(v_as_4735_);
    return v_res_4741_;
}
pub unsafe fn l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(
    mut v_f_4742_: *mut leanh::LeanObject,
    mut v_init_4743_: *mut leanh::LeanObject,
    mut v_m_4744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_u2081_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: u8 = 0;
    v_map_u2081_4745_ = leanh::lean_ctor_get(v_m_4744_, 0);
    v_map_u2082_4746_ = leanh::lean_ctor_get(v_m_4744_, 1);
    v_buckets_4747_ = leanh::lean_ctor_get(v_map_u2081_4745_, 1);
    v___x_4748_ = leanh::lean_unsigned_to_nat(0);
    v___x_4749_ = lean_array_get_size(v_buckets_4747_);
    v___x_4750_ = lean_nat_dec_lt(v___x_4748_, v___x_4749_);
    if v___x_4750_ == 0 {
        let mut v___x_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4751_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_4746_, v_f_4742_, v_init_4743_);
        return v___x_4751_;
    } else {
        let mut v___x_4752_: u8 = 0;
        v___x_4752_ = lean_nat_dec_le(v___x_4749_, v___x_4749_);
        if v___x_4752_ == 0 {
            if v___x_4750_ == 0 {
                let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4753_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_4746_, v_f_4742_, v_init_4743_);
                return v___x_4753_;
            } else {
                let mut v___x_4754_: usize = 0;
                let mut v___x_4755_: usize = 0;
                let mut v___x_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4754_ = 0usize;
                v___x_4755_ = lean_usize_of_nat(v___x_4749_);
                leanh::lean_inc(v_f_4742_);
                v___x_4756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_4742_, v_buckets_4747_, v___x_4754_, v___x_4755_, v_init_4743_);
                v___x_4757_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_4746_, v_f_4742_, v___x_4756_);
                return v___x_4757_;
            }
        } else {
            let mut v___x_4758_: usize = 0;
            let mut v___x_4759_: usize = 0;
            let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4758_ = 0usize;
            v___x_4759_ = lean_usize_of_nat(v___x_4749_);
            leanh::lean_inc(v_f_4742_);
            v___x_4760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_4742_, v_buckets_4747_, v___x_4758_, v___x_4759_, v_init_4743_);
            v___x_4761_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_4746_, v_f_4742_, v___x_4760_);
            return v___x_4761_;
        }
    }
}
pub unsafe fn l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg___boxed(
    mut v_f_4762_: *mut leanh::LeanObject,
    mut v_init_4763_: *mut leanh::LeanObject,
    mut v_m_4764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4765_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(
        v_f_4762_,
        v_init_4763_,
        v_m_4764_,
    );
    leanh::lean_dec_ref(v_m_4764_);
    return v_res_4765_;
}
pub unsafe fn l_Lean_getRevAliases(
    mut v_env_4766_: *mut leanh::LeanObject,
    mut v_e_4767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4768_ = l_Lean_aliasExtension;
    v_toEnvExtension_4769_ = leanh::lean_ctor_get(v___x_4768_, 0);
    v_asyncMode_4770_ = leanh::lean_ctor_get(v_toEnvExtension_4769_, 2);
    v___f_4771_ = leanh::lean_alloc_closure(
        l_Lean_getRevAliases___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4771_, 0, v_e_4767_);
    v___x_4772_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_getAliasState___closed__2),
        core::ptr::addr_of_mut!(l_Lean_getAliasState___closed__2_once),
        _init_l_Lean_getAliasState___closed__2,
    );
    v___x_4773_ = leanh::lean_box(0);
    v___x_4774_ = leanh::lean_box(0);
    v___x_4775_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_4772_,
        v___x_4768_,
        v_env_4766_,
        v_asyncMode_4770_,
        v___x_4774_,
    );
    v___x_4776_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(
        v___f_4771_,
        v___x_4773_,
        v___x_4775_,
    );
    leanh::lean_dec(v___x_4775_);
    return v___x_4776_;
}
pub unsafe fn l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(
    mut v_00_u03b2_4777_: *mut leanh::LeanObject,
    mut v_00_u03c3_4778_: *mut leanh::LeanObject,
    mut v_f_4779_: *mut leanh::LeanObject,
    mut v_init_4780_: *mut leanh::LeanObject,
    mut v_m_4781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4782_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(
        v_f_4779_,
        v_init_4780_,
        v_m_4781_,
    );
    return v___x_4782_;
}
pub unsafe fn l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___boxed(
    mut v_00_u03b2_4783_: *mut leanh::LeanObject,
    mut v_00_u03c3_4784_: *mut leanh::LeanObject,
    mut v_f_4785_: *mut leanh::LeanObject,
    mut v_init_4786_: *mut leanh::LeanObject,
    mut v_m_4787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4788_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(
        v_00_u03b2_4783_,
        v_00_u03c3_4784_,
        v_f_4785_,
        v_init_4786_,
        v_m_4787_,
    );
    leanh::lean_dec_ref(v_m_4787_);
    return v_res_4788_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0(
    mut v_00_u03b2_4789_: *mut leanh::LeanObject,
    mut v_00_u03c3_4790_: *mut leanh::LeanObject,
    mut v_f_4791_: *mut leanh::LeanObject,
    mut v_x_4792_: *mut leanh::LeanObject,
    mut v_x_4793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4794_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_4791_, v_x_4792_, v_x_4793_);
    return v___x_4794_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(
    mut v_00_u03c3_4795_: *mut leanh::LeanObject,
    mut v_00_u03b2_4796_: *mut leanh::LeanObject,
    mut v_map_4797_: *mut leanh::LeanObject,
    mut v_f_4798_: *mut leanh::LeanObject,
    mut v_init_4799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4800_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_4797_, v_f_4798_, v_init_4799_);
    return v___x_4800_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___boxed(
    mut v_00_u03c3_4801_: *mut leanh::LeanObject,
    mut v_00_u03b2_4802_: *mut leanh::LeanObject,
    mut v_map_4803_: *mut leanh::LeanObject,
    mut v_f_4804_: *mut leanh::LeanObject,
    mut v_init_4805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4806_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(v_00_u03c3_4801_, v_00_u03b2_4802_, v_map_4803_, v_f_4804_, v_init_4805_);
    leanh::lean_dec_ref(v_map_4803_);
    return v_res_4806_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(
    mut v_00_u03b2_4807_: *mut leanh::LeanObject,
    mut v_00_u03c3_4808_: *mut leanh::LeanObject,
    mut v_f_4809_: *mut leanh::LeanObject,
    mut v_as_4810_: *mut leanh::LeanObject,
    mut v_i_4811_: usize,
    mut v_stop_4812_: usize,
    mut v_b_4813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_4809_, v_as_4810_, v_i_4811_, v_stop_4812_, v_b_4813_);
    return v___x_4814_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___boxed(
    mut v_00_u03b2_4815_: *mut leanh::LeanObject,
    mut v_00_u03c3_4816_: *mut leanh::LeanObject,
    mut v_f_4817_: *mut leanh::LeanObject,
    mut v_as_4818_: *mut leanh::LeanObject,
    mut v_i_4819_: *mut leanh::LeanObject,
    mut v_stop_4820_: *mut leanh::LeanObject,
    mut v_b_4821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4822_: usize = 0;
    let mut v_stop_boxed_4823_: usize = 0;
    let mut v_res_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4822_ = leanh::lean_unbox_usize(v_i_4819_);
    leanh::lean_dec(v_i_4819_);
    v_stop_boxed_4823_ = leanh::lean_unbox_usize(v_stop_4820_);
    leanh::lean_dec(v_stop_4820_);
    v_res_4824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(v_00_u03b2_4815_, v_00_u03c3_4816_, v_f_4817_, v_as_4818_, v_i_boxed_4822_, v_stop_boxed_4823_, v_b_4821_);
    leanh::lean_dec_ref(v_as_4818_);
    return v_res_4824_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(
    mut v_map_4825_: *mut leanh::LeanObject,
    mut v_f_4826_: *mut leanh::LeanObject,
    mut v_init_4827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4828_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_4826_, v_map_4825_, v_init_4827_);
    return v___x_4828_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_map_4829_: *mut leanh::LeanObject,
    mut v_f_4830_: *mut leanh::LeanObject,
    mut v_init_4831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4832_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(v_map_4829_, v_f_4830_, v_init_4831_);
    leanh::lean_dec_ref(v_map_4829_);
    return v_res_4832_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(
    mut v_00_u03c3_4833_: *mut leanh::LeanObject,
    mut v_00_u03b2_4834_: *mut leanh::LeanObject,
    mut v_map_4835_: *mut leanh::LeanObject,
    mut v_f_4836_: *mut leanh::LeanObject,
    mut v_init_4837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4838_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_4836_, v_map_4835_, v_init_4837_);
    return v___x_4838_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03c3_4839_: *mut leanh::LeanObject,
    mut v_00_u03b2_4840_: *mut leanh::LeanObject,
    mut v_map_4841_: *mut leanh::LeanObject,
    mut v_f_4842_: *mut leanh::LeanObject,
    mut v_init_4843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4844_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(v_00_u03c3_4839_, v_00_u03b2_4840_, v_map_4841_, v_f_4842_, v_init_4843_);
    leanh::lean_dec_ref(v_map_4841_);
    return v_res_4844_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03c3_4845_: *mut leanh::LeanObject,
    mut v_00_u03b1_4846_: *mut leanh::LeanObject,
    mut v_00_u03b2_4847_: *mut leanh::LeanObject,
    mut v_f_4848_: *mut leanh::LeanObject,
    mut v_x_4849_: *mut leanh::LeanObject,
    mut v_x_4850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4851_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_4848_, v_x_4849_, v_x_4850_);
    return v___x_4851_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03c3_4852_: *mut leanh::LeanObject,
    mut v_00_u03b1_4853_: *mut leanh::LeanObject,
    mut v_00_u03b2_4854_: *mut leanh::LeanObject,
    mut v_f_4855_: *mut leanh::LeanObject,
    mut v_x_4856_: *mut leanh::LeanObject,
    mut v_x_4857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4858_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(v_00_u03c3_4852_, v_00_u03b1_4853_, v_00_u03b2_4854_, v_f_4855_, v_x_4856_, v_x_4857_);
    leanh::lean_dec_ref(v_x_4856_);
    return v_res_4858_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(
    mut v_00_u03b1_4859_: *mut leanh::LeanObject,
    mut v_00_u03b2_4860_: *mut leanh::LeanObject,
    mut v_00_u03c3_4861_: *mut leanh::LeanObject,
    mut v_f_4862_: *mut leanh::LeanObject,
    mut v_as_4863_: *mut leanh::LeanObject,
    mut v_i_4864_: usize,
    mut v_stop_4865_: usize,
    mut v_b_4866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_4862_, v_as_4863_, v_i_4864_, v_stop_4865_, v_b_4866_);
    return v___x_4867_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(
    mut v_00_u03b1_4868_: *mut leanh::LeanObject,
    mut v_00_u03b2_4869_: *mut leanh::LeanObject,
    mut v_00_u03c3_4870_: *mut leanh::LeanObject,
    mut v_f_4871_: *mut leanh::LeanObject,
    mut v_as_4872_: *mut leanh::LeanObject,
    mut v_i_4873_: *mut leanh::LeanObject,
    mut v_stop_4874_: *mut leanh::LeanObject,
    mut v_b_4875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4876_: usize = 0;
    let mut v_stop_boxed_4877_: usize = 0;
    let mut v_res_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4876_ = leanh::lean_unbox_usize(v_i_4873_);
    leanh::lean_dec(v_i_4873_);
    v_stop_boxed_4877_ = leanh::lean_unbox_usize(v_stop_4874_);
    leanh::lean_dec(v_stop_4874_);
    v_res_4878_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_4868_, v_00_u03b2_4869_, v_00_u03c3_4870_, v_f_4871_, v_as_4872_, v_i_boxed_4876_, v_stop_boxed_4877_, v_b_4875_);
    leanh::lean_dec_ref(v_as_4872_);
    return v_res_4878_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(
    mut v_00_u03c3_4879_: *mut leanh::LeanObject,
    mut v_00_u03b1_4880_: *mut leanh::LeanObject,
    mut v_00_u03b2_4881_: *mut leanh::LeanObject,
    mut v_f_4882_: *mut leanh::LeanObject,
    mut v_keys_4883_: *mut leanh::LeanObject,
    mut v_vals_4884_: *mut leanh::LeanObject,
    mut v_heq_4885_: *mut leanh::LeanObject,
    mut v_i_4886_: *mut leanh::LeanObject,
    mut v_acc_4887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4888_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_4882_, v_keys_4883_, v_vals_4884_, v_i_4886_, v_acc_4887_);
    return v___x_4888_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___boxed(
    mut v_00_u03c3_4889_: *mut leanh::LeanObject,
    mut v_00_u03b1_4890_: *mut leanh::LeanObject,
    mut v_00_u03b2_4891_: *mut leanh::LeanObject,
    mut v_f_4892_: *mut leanh::LeanObject,
    mut v_keys_4893_: *mut leanh::LeanObject,
    mut v_vals_4894_: *mut leanh::LeanObject,
    mut v_heq_4895_: *mut leanh::LeanObject,
    mut v_i_4896_: *mut leanh::LeanObject,
    mut v_acc_4897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4898_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(v_00_u03c3_4889_, v_00_u03b1_4890_, v_00_u03b2_4891_, v_f_4892_, v_keys_4893_, v_vals_4894_, v_heq_4895_, v_i_4896_, v_acc_4897_);
    leanh::lean_dec_ref(v_vals_4894_);
    leanh::lean_dec_ref(v_keys_4893_);
    return v_res_4898_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(
    mut v_env_4899_: *mut leanh::LeanObject,
    mut v_declName_4900_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_4902_: u8 = 0;
    let mut v___x_4903_: u8 = 0;
    let mut v___x_4904_: u8 = 0;
    let mut v___x_4905_: u8 = 0;
    let mut v___x_4906_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4905_ = l_Lean_Environment_containsOnBranch(v_env_4899_, v_declName_4900_);
                if v___x_4905_ == 0 {
                    leanh::lean_inc(v_declName_4900_);
                    leanh::lean_inc_ref(v_env_4899_);
                    v___x_4906_ = lean_is_reserved_name(v_env_4899_, v_declName_4900_);
                    v___y_4902_ = v___x_4906_;
                    state = 1;
                    continue;
                } else {
                    v___y_4902_ = v___x_4905_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4902_ == 0 {
                    v___x_4903_ = 1;
                    v___x_4904_ =
                        l_Lean_Environment_contains(v_env_4899_, v_declName_4900_, v___x_4903_);
                    return v___x_4904_;
                } else {
                    leanh::lean_dec(v_declName_4900_);
                    leanh::lean_dec_ref(v_env_4899_);
                    return v___y_4902_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(
    mut v_env_4907_: *mut leanh::LeanObject,
    mut v_declName_4908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4909_: u8 = 0;
    let mut v_r_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4909_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(
        v_env_4907_,
        v_declName_4908_,
    );
    v_r_4910_ = leanh::lean_box((v_res_4909_) as usize);
    return v_r_4910_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(
    mut v_name_4911_: *mut leanh::LeanObject,
    mut v_decl_4912_: *mut leanh::LeanObject,
    mut v_ref_4913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: u8 = 0;
    let mut v___x_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4924_: u8 = 0;
    let mut v___x_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4929_: u8 = 0;
    let mut v_unused_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4934_: u8 = 0;
    let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_4915_ = leanh::lean_ctor_get(v_decl_4912_, 0);
                v_descr_4916_ = leanh::lean_ctor_get(v_decl_4912_, 1);
                v_deprecation_x3f_4917_ = leanh::lean_ctor_get(v_decl_4912_, 2);
                v___x_4918_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_4919_ = (leanh::lean_unbox(v_defValue_4915_) as u8);
                leanh::lean_ctor_set_uint8(v___x_4918_, 0 as u32, v___x_4919_);
                leanh::lean_inc(v_deprecation_x3f_4917_);
                leanh::lean_inc_ref(v_descr_4916_);
                leanh::lean_inc_n(v_name_4911_, 2);
                v___x_4920_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_4920_, 0, v_name_4911_);
                leanh::lean_ctor_set(v___x_4920_, 1, v_ref_4913_);
                leanh::lean_ctor_set(v___x_4920_, 2, v___x_4918_);
                leanh::lean_ctor_set(v___x_4920_, 3, v_descr_4916_);
                leanh::lean_ctor_set(v___x_4920_, 4, v_deprecation_x3f_4917_);
                v___x_4921_ = lean_register_option(v_name_4911_, v___x_4920_);
                if leanh::lean_obj_tag(v___x_4921_) == 0 {
                    v_isSharedCheck_4929_ = (!leanh::lean_is_exclusive(v___x_4921_)) as u8;
                    if v_isSharedCheck_4929_ == 0 {
                        v_unused_4930_ = leanh::lean_ctor_get(v___x_4921_, 0);
                        leanh::lean_dec(v_unused_4930_);
                        v___x_4923_ = v___x_4921_;
                        v_isShared_4924_ = v_isSharedCheck_4929_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4921_);
                        v___x_4923_ = leanh::lean_box(0);
                        v_isShared_4924_ = v_isSharedCheck_4929_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_4911_);
                    v_a_4931_ = leanh::lean_ctor_get(v___x_4921_, 0);
                    v_isSharedCheck_4938_ = (!leanh::lean_is_exclusive(v___x_4921_)) as u8;
                    if v_isSharedCheck_4938_ == 0 {
                        v___x_4933_ = v___x_4921_;
                        v_isShared_4934_ = v_isSharedCheck_4938_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4931_);
                        leanh::lean_dec(v___x_4921_);
                        v___x_4933_ = leanh::lean_box(0);
                        v_isShared_4934_ = v_isSharedCheck_4938_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_defValue_4915_);
                v___x_4925_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4925_, 0, v_name_4911_);
                leanh::lean_ctor_set(v___x_4925_, 1, v_defValue_4915_);
                if v_isShared_4924_ == 0 {
                    leanh::lean_ctor_set(v___x_4923_, 0, v___x_4925_);
                    v___x_4927_ = v___x_4923_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4928_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4928_, 0, v___x_4925_);
                    v___x_4927_ = v_reuseFailAlloc_4928_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4927_;
            }
            3 => {
                if v_isShared_4934_ == 0 {
                    v___x_4936_ = v___x_4933_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4937_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_a_4931_);
                    v___x_4936_ = v_reuseFailAlloc_4937_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4936_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_4939_: *mut leanh::LeanObject,
    mut v_decl_4940_: *mut leanh::LeanObject,
    mut v_ref_4941_: *mut leanh::LeanObject,
    mut v_a_4942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4943_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v_name_4939_, v_decl_4940_, v_ref_4941_);
    leanh::lean_dec_ref(v_decl_4940_);
    return v_res_4943_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4962_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_;
    v___x_4963_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_;
    v___x_4964_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_;
    v___x_4965_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_4962_, v___x_4963_, v___x_4964_);
    return v___x_4965_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4____boxed(
    mut v_a_4966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4967_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
    return v_res_4967_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4986_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_;
    v___x_4987_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_;
    v___x_4988_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_;
    v___x_4989_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_4986_, v___x_4987_, v___x_4988_);
    return v___x_4989_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4____boxed(
    mut v_a_4990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4991_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
    return v_res_4991_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(
    mut v_opts_4992_: *mut leanh::LeanObject,
    mut v_opt_4993_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_4994_ = leanh::lean_ctor_get(v_opt_4993_, 0);
    v_defValue_4995_ = leanh::lean_ctor_get(v_opt_4993_, 1);
    v_map_4996_ = leanh::lean_ctor_get(v_opts_4992_, 0);
    v___x_4997_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4996_,
            v_name_4994_,
        );
    if leanh::lean_obj_tag(v___x_4997_) == 0 {
        let mut v___x_4998_: u8 = 0;
        v___x_4998_ = (leanh::lean_unbox(v_defValue_4995_) as u8);
        return v___x_4998_;
    } else {
        let mut v_val_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4999_ = leanh::lean_ctor_get(v___x_4997_, 0);
        leanh::lean_inc(v_val_4999_);
        leanh::lean_dec_ref_known(v___x_4997_, 1);
        if leanh::lean_obj_tag(v_val_4999_) == 1 {
            let mut v_v_5000_: u8 = 0;
            v_v_5000_ = leanh::lean_ctor_get_uint8(v_val_4999_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_4999_, 0);
            return v_v_5000_;
        } else {
            let mut v___x_5001_: u8 = 0;
            leanh::lean_dec(v_val_4999_);
            v___x_5001_ = (leanh::lean_unbox(v_defValue_4995_) as u8);
            return v___x_5001_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1___boxed(
    mut v_opts_5002_: *mut leanh::LeanObject,
    mut v_opt_5003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5004_: u8 = 0;
    let mut v_r_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5004_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_5002_, v_opt_5003_);
    leanh::lean_dec_ref(v_opt_5003_);
    leanh::lean_dec_ref(v_opts_5002_);
    v_r_5005_ = leanh::lean_box((v_res_5004_) as usize);
    return v_r_5005_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(
    mut v_declName_5009_: *mut leanh::LeanObject,
    mut v_env_5010_: *mut leanh::LeanObject,
    mut v_as_5011_: *mut leanh::LeanObject,
    mut v_sz_5012_: usize,
    mut v_i_5013_: usize,
    mut v_b_5014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5015_: u8 = 0;
    let mut v_a_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: u8 = 0;
    let mut v___x_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: usize = 0;
    let mut v___x_5024_: usize = 0;
    let mut v___x_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5015_ = lean_usize_dec_lt(v_i_5013_, v_sz_5012_);
                if v___x_5015_ == 0 {
                    leanh::lean_dec_ref(v_env_5010_);
                    leanh::lean_dec(v_declName_5009_);
                    leanh::lean_inc_ref(v_b_5014_);
                    return v_b_5014_;
                } else {
                    v_a_5016_ = lean_array_uget_borrowed(v_as_5011_, v_i_5013_);
                    v_toImport_5017_ = leanh::lean_ctor_get(v_a_5016_, 0);
                    v_module_5018_ = leanh::lean_ctor_get(v_toImport_5017_, 0);
                    v___x_5019_ = leanh::lean_box(0);
                    leanh::lean_inc(v_declName_5009_);
                    leanh::lean_inc(v_module_5018_);
                    v___x_5020_ = l_Lean_mkPrivateNameCore(v_module_5018_, v_declName_5009_);
                    leanh::lean_inc(v___x_5020_);
                    leanh::lean_inc_ref(v_env_5010_);
                    v___x_5021_ =
                        l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(
                            v_env_5010_,
                            v___x_5020_,
                        );
                    if v___x_5021_ == 0 {
                        leanh::lean_dec(v___x_5020_);
                        v___x_5022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0;
                        v___x_5023_ = 1usize;
                        v___x_5024_ = lean_usize_add(v_i_5013_, v___x_5023_);
                        v_i_5013_ = v___x_5024_;
                        v_b_5014_ = v___x_5022_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_env_5010_);
                        leanh::lean_dec(v_declName_5009_);
                        v___x_5026_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5026_, 0, v___x_5020_);
                        v___x_5027_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5027_, 0, v___x_5026_);
                        v___x_5028_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5028_, 0, v___x_5027_);
                        leanh::lean_ctor_set(v___x_5028_, 1, v___x_5019_);
                        return v___x_5028_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___boxed(
    mut v_declName_5029_: *mut leanh::LeanObject,
    mut v_env_5030_: *mut leanh::LeanObject,
    mut v_as_5031_: *mut leanh::LeanObject,
    mut v_sz_5032_: *mut leanh::LeanObject,
    mut v_i_5033_: *mut leanh::LeanObject,
    mut v_b_5034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5035_: usize = 0;
    let mut v_i_boxed_5036_: usize = 0;
    let mut v_res_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5035_ = leanh::lean_unbox_usize(v_sz_5032_);
    leanh::lean_dec(v_sz_5032_);
    v_i_boxed_5036_ = leanh::lean_unbox_usize(v_i_5033_);
    leanh::lean_dec(v_i_5033_);
    v_res_5037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_5029_, v_env_5030_, v_as_5031_, v_sz_boxed_5035_, v_i_boxed_5036_, v_b_5034_);
    leanh::lean_dec_ref(v_b_5034_);
    leanh::lean_dec_ref(v_as_5031_);
    return v_res_5037_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(
    mut v_env_5038_: *mut leanh::LeanObject,
    mut v_opts_5039_: *mut leanh::LeanObject,
    mut v_declName_5040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: u8 = 0;
    let mut v___x_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_5045_: u8 = 0;
    let mut v___x_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_importAllModules_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5050_: usize = 0;
    let mut v___x_5051_: usize = 0;
    let mut v___x_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_5056_: u8 = 0;
    let mut v___x_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: u8 = 0;
    let mut v___x_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isExporting_5056_ = leanh::lean_ctor_get_uint8(
                    v_env_5038_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                if v_isExporting_5056_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_5057_ = l_Lean_ResolveName_backward_privateInPublic;
                    v___x_5058_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_5039_, v___x_5057_);
                    if v___x_5058_ == 0 {
                        leanh::lean_dec(v_declName_5040_);
                        leanh::lean_dec_ref(v_env_5038_);
                        v___x_5059_ = leanh::lean_box(0);
                        return v___x_5059_;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_declName_5040_);
                v___x_5042_ = l_Lean_mkPrivateName(v_env_5038_, v_declName_5040_);
                leanh::lean_inc(v___x_5042_);
                leanh::lean_inc_ref(v_env_5038_);
                v___x_5043_ =
                    l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(
                        v_env_5038_,
                        v___x_5042_,
                    );
                if v___x_5043_ == 0 {
                    leanh::lean_dec(v___x_5042_);
                    v___x_5044_ = l_Lean_Environment_header(v_env_5038_);
                    v_isModule_5045_ = leanh::lean_ctor_get_uint8(
                        v___x_5044_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 4) as u32,
                    );
                    if v_isModule_5045_ == 0 {
                        leanh::lean_dec_ref(v___x_5044_);
                        leanh::lean_dec(v_declName_5040_);
                        leanh::lean_dec_ref(v_env_5038_);
                        v___x_5046_ = leanh::lean_box(0);
                        return v___x_5046_;
                    } else {
                        v_importAllModules_5047_ = leanh::lean_ctor_get(v___x_5044_, 5);
                        leanh::lean_inc_ref(v_importAllModules_5047_);
                        leanh::lean_dec_ref(v___x_5044_);
                        v___x_5048_ = leanh::lean_box(0);
                        v___x_5049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0;
                        v_sz_5050_ = lean_array_size(v_importAllModules_5047_);
                        v___x_5051_ = 0usize;
                        v___x_5052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_5040_, v_env_5038_, v_importAllModules_5047_, v_sz_5050_, v___x_5051_, v___x_5049_);
                        leanh::lean_dec_ref(v_importAllModules_5047_);
                        v_fst_5053_ = leanh::lean_ctor_get(v___x_5052_, 0);
                        leanh::lean_inc(v_fst_5053_);
                        leanh::lean_dec_ref(v___x_5052_);
                        if leanh::lean_obj_tag(v_fst_5053_) == 0 {
                            return v___x_5048_;
                        } else {
                            v_val_5054_ = leanh::lean_ctor_get(v_fst_5053_, 0);
                            leanh::lean_inc(v_val_5054_);
                            leanh::lean_dec_ref_known(v_fst_5053_, 1);
                            return v_val_5054_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_declName_5040_);
                    leanh::lean_dec_ref(v_env_5038_);
                    v___x_5055_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5055_, 0, v___x_5042_);
                    return v___x_5055_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___boxed(
    mut v_env_5060_: *mut leanh::LeanObject,
    mut v_opts_5061_: *mut leanh::LeanObject,
    mut v_declName_5062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5063_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(
        v_env_5060_,
        v_opts_5061_,
        v_declName_5062_,
    );
    leanh::lean_dec_ref(v_opts_5061_);
    return v_res_5063_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(
    mut v_env_5064_: *mut leanh::LeanObject,
    mut v_opts_5065_: *mut leanh::LeanObject,
    mut v_ns_5066_: *mut leanh::LeanObject,
    mut v_id_5067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_resolvedId_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: u8 = 0;
    let mut v_resolvedIds_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: u8 = 0;
    let mut v___x_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_id_5067_);
                v_resolvedId_5068_ = l_Lean_Name_append(v_ns_5066_, v_id_5067_);
                v___x_5069_ = l_Lean_Name_isAtomic(v_id_5067_);
                leanh::lean_dec(v_id_5067_);
                leanh::lean_inc_ref(v_env_5064_);
                v_resolvedIds_5070_ =
                    l_Lean_getAliases(v_env_5064_, v_resolvedId_5068_, v___x_5069_);
                if v___x_5069_ == 0 {
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_resolvedId_5068_);
                    leanh::lean_inc_ref(v_env_5064_);
                    v___x_5077_ = l_Lean_isProtected(v_env_5064_, v_resolvedId_5068_);
                    if v___x_5077_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_resolvedId_5068_);
                        leanh::lean_dec_ref(v_env_5064_);
                        return v_resolvedIds_5070_;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_resolvedId_5068_);
                leanh::lean_inc_ref(v_env_5064_);
                v___x_5072_ =
                    l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(
                        v_env_5064_,
                        v_resolvedId_5068_,
                    );
                if v___x_5072_ == 0 {
                    v___x_5073_ =
                        l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(
                            v_env_5064_,
                            v_opts_5065_,
                            v_resolvedId_5068_,
                        );
                    if leanh::lean_obj_tag(v___x_5073_) == 1 {
                        v_val_5074_ = leanh::lean_ctor_get(v___x_5073_, 0);
                        leanh::lean_inc(v_val_5074_);
                        leanh::lean_dec_ref_known(v___x_5073_, 1);
                        v___x_5075_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5075_, 0, v_val_5074_);
                        leanh::lean_ctor_set(v___x_5075_, 1, v_resolvedIds_5070_);
                        return v___x_5075_;
                    } else {
                        leanh::lean_dec(v___x_5073_);
                        return v_resolvedIds_5070_;
                    }
                } else {
                    leanh::lean_dec_ref(v_env_5064_);
                    v___x_5076_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5076_, 0, v_resolvedId_5068_);
                    leanh::lean_ctor_set(v___x_5076_, 1, v_resolvedIds_5070_);
                    return v___x_5076_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName___boxed(
    mut v_env_5078_: *mut leanh::LeanObject,
    mut v_opts_5079_: *mut leanh::LeanObject,
    mut v_ns_5080_: *mut leanh::LeanObject,
    mut v_id_5081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5082_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(
        v_env_5078_,
        v_opts_5079_,
        v_ns_5080_,
        v_id_5081_,
    );
    leanh::lean_dec_ref(v_opts_5079_);
    return v_res_5082_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(
    mut v_env_5083_: *mut leanh::LeanObject,
    mut v_opts_5084_: *mut leanh::LeanObject,
    mut v_id_5085_: *mut leanh::LeanObject,
    mut v_x_5086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pre_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5086_) == 1 {
                    v_pre_5087_ = leanh::lean_ctor_get(v_x_5086_, 0);
                    leanh::lean_inc(v_pre_5087_);
                    leanh::lean_inc(v_id_5085_);
                    leanh::lean_inc_ref(v_env_5083_);
                    v___x_5088_ =
                        l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(
                            v_env_5083_,
                            v_opts_5084_,
                            v_x_5086_,
                            v_id_5085_,
                        );
                    if leanh::lean_obj_tag(v___x_5088_) == 0 {
                        v_x_5086_ = v_pre_5087_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_pre_5087_);
                        leanh::lean_dec(v_id_5085_);
                        leanh::lean_dec_ref(v_env_5083_);
                        return v___x_5088_;
                    }
                } else {
                    leanh::lean_dec(v_x_5086_);
                    leanh::lean_dec(v_id_5085_);
                    leanh::lean_dec_ref(v_env_5083_);
                    v___x_5090_ = leanh::lean_box(0);
                    return v___x_5090_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace___boxed(
    mut v_env_5091_: *mut leanh::LeanObject,
    mut v_opts_5092_: *mut leanh::LeanObject,
    mut v_id_5093_: *mut leanh::LeanObject,
    mut v_x_5094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5095_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(
        v_env_5091_,
        v_opts_5092_,
        v_id_5093_,
        v_x_5094_,
    );
    leanh::lean_dec_ref(v_opts_5092_);
    return v_res_5095_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(
    mut v_env_5096_: *mut leanh::LeanObject,
    mut v_opts_5097_: *mut leanh::LeanObject,
    mut v_id_5098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5099_: u8 = 0;
    v___x_5099_ = l_Lean_Name_isAtomic(v_id_5098_);
    if v___x_5099_ == 0 {
        let mut v___x_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_resolvedId_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5103_: u8 = 0;
        v___x_5100_ = l_Lean_rootNamespace;
        v___x_5101_ = leanh::lean_box(0);
        v_resolvedId_5102_ = l_Lean_Name_replacePrefix(v_id_5098_, v___x_5100_, v___x_5101_);
        leanh::lean_inc(v_resolvedId_5102_);
        leanh::lean_inc_ref(v_env_5096_);
        v___x_5103_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(
            v_env_5096_,
            v_resolvedId_5102_,
        );
        if v___x_5103_ == 0 {
            let mut v___x_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5104_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(
                v_env_5096_,
                v_opts_5097_,
                v_resolvedId_5102_,
            );
            return v___x_5104_;
        } else {
            let mut v___x_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_env_5096_);
            v___x_5105_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_5105_, 0, v_resolvedId_5102_);
            return v___x_5105_;
        }
    } else {
        let mut v___x_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_id_5098_);
        leanh::lean_dec_ref(v_env_5096_);
        v___x_5106_ = leanh::lean_box(0);
        return v___x_5106_;
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___boxed(
    mut v_env_5107_: *mut leanh::LeanObject,
    mut v_opts_5108_: *mut leanh::LeanObject,
    mut v_id_5109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5110_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(
        v_env_5107_,
        v_opts_5108_,
        v_id_5109_,
    );
    leanh::lean_dec_ref(v_opts_5108_);
    return v_res_5110_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(
    mut v_env_5111_: *mut leanh::LeanObject,
    mut v_opts_5112_: *mut leanh::LeanObject,
    mut v_id_5113_: *mut leanh::LeanObject,
    mut v_x_5114_: *mut leanh::LeanObject,
    mut v_x_5115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ns_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_except_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: u8 = 0;
    let mut v_newResolvedIds_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5128_: u8 = 0;
    let mut v_id_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: u8 = 0;
    let mut v___x_5132_: u8 = 0;
    let mut v_candidate_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: u8 = 0;
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5145_: u8 = 0;
    let mut v_unused_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5114_) == 0 {
                    leanh::lean_dec(v_id_5113_);
                    leanh::lean_dec_ref(v_env_5111_);
                    return v_x_5115_;
                } else {
                    v_head_5116_ = leanh::lean_ctor_get(v_x_5114_, 0);
                    leanh::lean_inc(v_head_5116_);
                    if leanh::lean_obj_tag(v_head_5116_) == 0 {
                        v_tail_5117_ = leanh::lean_ctor_get(v_x_5114_, 1);
                        leanh::lean_inc(v_tail_5117_);
                        leanh::lean_dec_ref_known(v_x_5114_, 2);
                        v_ns_5118_ = leanh::lean_ctor_get(v_head_5116_, 0);
                        leanh::lean_inc(v_ns_5118_);
                        v_except_5119_ = leanh::lean_ctor_get(v_head_5116_, 1);
                        leanh::lean_inc(v_except_5119_);
                        leanh::lean_dec_ref_known(v_head_5116_, 2);
                        v___x_5120_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(
                            v_id_5113_,
                            v_except_5119_,
                        );
                        leanh::lean_dec(v_except_5119_);
                        if v___x_5120_ == 0 {
                            leanh::lean_inc(v_id_5113_);
                            leanh::lean_inc_ref(v_env_5111_);
                            v_newResolvedIds_5121_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_5111_, v_opts_5112_, v_ns_5118_, v_id_5113_);
                            v___x_5122_ =
                                l_List_appendTR___redArg(v_newResolvedIds_5121_, v_x_5115_);
                            v_x_5114_ = v_tail_5117_;
                            v_x_5115_ = v___x_5122_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_ns_5118_);
                            v_x_5114_ = v_tail_5117_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_tail_5125_ = leanh::lean_ctor_get(v_x_5114_, 1);
                        v_isSharedCheck_5145_ = (!leanh::lean_is_exclusive(v_x_5114_)) as u8;
                        if v_isSharedCheck_5145_ == 0 {
                            v_unused_5146_ = leanh::lean_ctor_get(v_x_5114_, 0);
                            leanh::lean_dec(v_unused_5146_);
                            v___x_5127_ = v_x_5114_;
                            v_isShared_5128_ = v_isSharedCheck_5145_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_tail_5125_);
                            leanh::lean_dec(v_x_5114_);
                            v___x_5127_ = leanh::lean_box(0);
                            v_isShared_5128_ = v_isSharedCheck_5145_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_id_5129_ = leanh::lean_ctor_get(v_head_5116_, 0);
                leanh::lean_inc(v_id_5129_);
                v_declName_5130_ = leanh::lean_ctor_get(v_head_5116_, 1);
                leanh::lean_inc(v_declName_5130_);
                leanh::lean_dec_ref_known(v_head_5116_, 2);
                v___x_5131_ = lean_name_eq(v_id_5129_, v_id_5113_);
                if v___x_5131_ == 0 {
                    v___x_5132_ = l_Lean_Name_isPrefixOf(v_id_5129_, v_id_5113_);
                    if v___x_5132_ == 0 {
                        leanh::lean_dec(v_declName_5130_);
                        leanh::lean_dec(v_id_5129_);
                        leanh::lean_del_object(v___x_5127_);
                        v_x_5114_ = v_tail_5125_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_id_5113_);
                        v_candidate_5134_ =
                            l_Lean_Name_replacePrefix(v_id_5113_, v_id_5129_, v_declName_5130_);
                        leanh::lean_dec(v_declName_5130_);
                        leanh::lean_dec(v_id_5129_);
                        leanh::lean_inc(v_candidate_5134_);
                        leanh::lean_inc_ref(v_env_5111_);
                        v___x_5135_ = l_Lean_Environment_contains(
                            v_env_5111_,
                            v_candidate_5134_,
                            v___x_5132_,
                        );
                        if v___x_5135_ == 0 {
                            leanh::lean_dec(v_candidate_5134_);
                            leanh::lean_del_object(v___x_5127_);
                            v_x_5114_ = v_tail_5125_;
                            state = 0;
                            continue;
                        } else {
                            if v_isShared_5128_ == 0 {
                                leanh::lean_ctor_set(v___x_5127_, 1, v_x_5115_);
                                leanh::lean_ctor_set(v___x_5127_, 0, v_candidate_5134_);
                                v___x_5138_ = v___x_5127_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_5140_ =
                                    leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_5140_,
                                    0,
                                    v_candidate_5134_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_5140_, 1, v_x_5115_);
                                v___x_5138_ = v_reuseFailAlloc_5140_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_id_5129_);
                    if v_isShared_5128_ == 0 {
                        leanh::lean_ctor_set(v___x_5127_, 1, v_x_5115_);
                        leanh::lean_ctor_set(v___x_5127_, 0, v_declName_5130_);
                        v___x_5142_ = v___x_5127_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5144_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5144_, 0, v_declName_5130_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5144_, 1, v_x_5115_);
                        v___x_5142_ = v_reuseFailAlloc_5144_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_5114_ = v_tail_5125_;
                v_x_5115_ = v___x_5138_;
                state = 0;
                continue;
            }
            3 => {
                v_x_5114_ = v_tail_5125_;
                v_x_5115_ = v___x_5142_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls___boxed(
    mut v_env_5147_: *mut leanh::LeanObject,
    mut v_opts_5148_: *mut leanh::LeanObject,
    mut v_id_5149_: *mut leanh::LeanObject,
    mut v_x_5150_: *mut leanh::LeanObject,
    mut v_x_5151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5152_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(
        v_env_5147_,
        v_opts_5148_,
        v_id_5149_,
        v_x_5150_,
        v_x_5151_,
    );
    leanh::lean_dec_ref(v_opts_5148_);
    return v_res_5152_;
}
pub unsafe fn l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(
    mut v_as_5154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5155_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0;
    v___x_5156_ = l_List_eraseDupsBy___redArg(v___f_5155_, v_as_5154_);
    return v___x_5156_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(
    mut v_projs_5157_: *mut leanh::LeanObject,
    mut v_a_5158_: *mut leanh::LeanObject,
    mut v_a_5159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5165_: u8 = 0;
    let mut v___x_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5171_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_5158_) == 0 {
                    leanh::lean_dec(v_projs_5157_);
                    v___x_5160_ = l_List_reverse___redArg(v_a_5159_);
                    return v___x_5160_;
                } else {
                    v_head_5161_ = leanh::lean_ctor_get(v_a_5158_, 0);
                    v_tail_5162_ = leanh::lean_ctor_get(v_a_5158_, 1);
                    v_isSharedCheck_5171_ = (!leanh::lean_is_exclusive(v_a_5158_)) as u8;
                    if v_isSharedCheck_5171_ == 0 {
                        v___x_5164_ = v_a_5158_;
                        v_isShared_5165_ = v_isSharedCheck_5171_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5162_);
                        leanh::lean_inc(v_head_5161_);
                        leanh::lean_dec(v_a_5158_);
                        v___x_5164_ = leanh::lean_box(0);
                        v_isShared_5165_ = v_isSharedCheck_5171_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_projs_5157_);
                v___x_5166_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5166_, 0, v_head_5161_);
                leanh::lean_ctor_set(v___x_5166_, 1, v_projs_5157_);
                if v_isShared_5165_ == 0 {
                    leanh::lean_ctor_set(v___x_5164_, 1, v_a_5159_);
                    leanh::lean_ctor_set(v___x_5164_, 0, v___x_5166_);
                    v___x_5168_ = v___x_5164_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5170_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 0, v___x_5166_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 1, v_a_5159_);
                    v___x_5168_ = v_reuseFailAlloc_5170_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5158_ = v_tail_5162_;
                v_a_5159_ = v___x_5168_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(
    mut v_env_5172_: *mut leanh::LeanObject,
    mut v_opts_5173_: *mut leanh::LeanObject,
    mut v_ns_5174_: *mut leanh::LeanObject,
    mut v_openDecls_5175_: *mut leanh::LeanObject,
    mut v_extractionResult_5176_: *mut leanh::LeanObject,
    mut v_id_5177_: *mut leanh::LeanObject,
    mut v_projs_5178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pre_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_imported_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resolvedIds_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: u8 = 0;
    let mut v___x_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resolvedIds_5191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: u8 = 0;
    let mut v___x_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_id_5177_) == 1 {
                    v_pre_5179_ = leanh::lean_ctor_get(v_id_5177_, 0);
                    leanh::lean_inc(v_pre_5179_);
                    v_str_5180_ = leanh::lean_ctor_get(v_id_5177_, 1);
                    leanh::lean_inc_ref(v_str_5180_);
                    v_imported_5181_ = leanh::lean_ctor_get(v_extractionResult_5176_, 1);
                    v_ctx_5182_ = leanh::lean_ctor_get(v_extractionResult_5176_, 2);
                    v_scopes_5183_ = leanh::lean_ctor_get(v_extractionResult_5176_, 3);
                    leanh::lean_inc(v_scopes_5183_);
                    leanh::lean_inc(v_ctx_5182_);
                    leanh::lean_inc(v_imported_5181_);
                    v___x_5184_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_5184_, 0, v_id_5177_);
                    leanh::lean_ctor_set(v___x_5184_, 1, v_imported_5181_);
                    leanh::lean_ctor_set(v___x_5184_, 2, v_ctx_5182_);
                    leanh::lean_ctor_set(v___x_5184_, 3, v_scopes_5183_);
                    v_id_5185_ = l_Lean_MacroScopesView_review(v___x_5184_);
                    leanh::lean_inc(v_ns_5174_);
                    leanh::lean_inc(v_id_5185_);
                    leanh::lean_inc_ref(v_env_5172_);
                    v___x_5197_ =
                        l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(
                            v_env_5172_,
                            v_opts_5173_,
                            v_id_5185_,
                            v_ns_5174_,
                        );
                    if leanh::lean_obj_tag(v___x_5197_) == 0 {
                        leanh::lean_inc(v_id_5185_);
                        leanh::lean_inc_ref(v_env_5172_);
                        v___x_5204_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(
                            v_env_5172_,
                            v_opts_5173_,
                            v_id_5185_,
                        );
                        if leanh::lean_obj_tag(v___x_5204_) == 0 {
                            leanh::lean_inc(v_id_5185_);
                            leanh::lean_inc_ref(v_env_5172_);
                            v___x_5205_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_5172_, v_id_5185_);
                            if v___x_5205_ == 0 {
                                v___y_5199_ = v___x_5197_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_id_5185_);
                                v___x_5206_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_5206_, 0, v_id_5185_);
                                leanh::lean_ctor_set(v___x_5206_, 1, v___x_5197_);
                                v___y_5199_ = v___x_5206_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_id_5185_);
                            leanh::lean_dec_ref(v_str_5180_);
                            leanh::lean_dec(v_pre_5179_);
                            leanh::lean_dec(v_openDecls_5175_);
                            leanh::lean_dec(v_ns_5174_);
                            leanh::lean_dec_ref(v_env_5172_);
                            v_val_5207_ = leanh::lean_ctor_get(v___x_5204_, 0);
                            leanh::lean_inc(v_val_5207_);
                            leanh::lean_dec_ref_known(v___x_5204_, 1);
                            v___x_5208_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5208_, 0, v_val_5207_);
                            leanh::lean_ctor_set(v___x_5208_, 1, v_projs_5178_);
                            v___x_5209_ = leanh::lean_box(0);
                            v___x_5210_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5210_, 0, v___x_5208_);
                            leanh::lean_ctor_set(v___x_5210_, 1, v___x_5209_);
                            return v___x_5210_;
                        }
                    } else {
                        leanh::lean_dec(v_id_5185_);
                        leanh::lean_dec_ref(v_str_5180_);
                        leanh::lean_dec(v_pre_5179_);
                        leanh::lean_dec(v_openDecls_5175_);
                        leanh::lean_dec(v_ns_5174_);
                        leanh::lean_dec_ref(v_env_5172_);
                        v___x_5211_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v___x_5197_);
                        v___x_5212_ = leanh::lean_box(0);
                        v___x_5213_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_5178_, v___x_5211_, v___x_5212_);
                        return v___x_5213_;
                    }
                } else {
                    leanh::lean_dec(v_projs_5178_);
                    leanh::lean_dec(v_id_5177_);
                    leanh::lean_dec(v_openDecls_5175_);
                    leanh::lean_dec(v_ns_5174_);
                    leanh::lean_dec_ref(v_env_5172_);
                    v___x_5214_ = leanh::lean_box(0);
                    return v___x_5214_;
                }
            }
            1 => {
                leanh::lean_inc(v_openDecls_5175_);
                leanh::lean_inc(v_id_5185_);
                leanh::lean_inc_ref_n(v_env_5172_, 2);
                v_resolvedIds_5188_ =
                    l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(
                        v_env_5172_,
                        v_opts_5173_,
                        v_id_5185_,
                        v_openDecls_5175_,
                        v___y_5187_,
                    );
                v___x_5189_ = l_Lean_Name_isAtomic(v_id_5185_);
                v___x_5190_ = l_Lean_getAliases(v_env_5172_, v_id_5185_, v___x_5189_);
                leanh::lean_dec(v_id_5185_);
                v_resolvedIds_5191_ = l_List_appendTR___redArg(v___x_5190_, v_resolvedIds_5188_);
                if leanh::lean_obj_tag(v_resolvedIds_5191_) == 0 {
                    v___x_5192_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5192_, 0, v_str_5180_);
                    leanh::lean_ctor_set(v___x_5192_, 1, v_projs_5178_);
                    v_id_5177_ = v_pre_5179_;
                    v_projs_5178_ = v___x_5192_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_str_5180_);
                    leanh::lean_dec(v_pre_5179_);
                    leanh::lean_dec(v_openDecls_5175_);
                    leanh::lean_dec(v_ns_5174_);
                    leanh::lean_dec_ref(v_env_5172_);
                    v___x_5194_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v_resolvedIds_5191_);
                    v___x_5195_ = leanh::lean_box(0);
                    v___x_5196_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_5178_, v___x_5194_, v___x_5195_);
                    return v___x_5196_;
                }
            }
            2 => {
                leanh::lean_inc(v_id_5185_);
                leanh::lean_inc_ref(v_env_5172_);
                v___x_5200_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(
                    v_env_5172_,
                    v_opts_5173_,
                    v_id_5185_,
                );
                if leanh::lean_obj_tag(v___x_5200_) == 1 {
                    v_val_5201_ = leanh::lean_ctor_get(v___x_5200_, 0);
                    leanh::lean_inc(v_val_5201_);
                    leanh::lean_dec_ref_known(v___x_5200_, 1);
                    v___x_5202_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5202_, 0, v_val_5201_);
                    leanh::lean_ctor_set(v___x_5202_, 1, v___x_5197_);
                    v___x_5203_ = l_List_appendTR___redArg(v___x_5202_, v___y_5199_);
                    v___y_5187_ = v___x_5203_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_5200_);
                    leanh::lean_dec(v___x_5197_);
                    v___y_5187_ = v___y_5199_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop___boxed(
    mut v_env_5215_: *mut leanh::LeanObject,
    mut v_opts_5216_: *mut leanh::LeanObject,
    mut v_ns_5217_: *mut leanh::LeanObject,
    mut v_openDecls_5218_: *mut leanh::LeanObject,
    mut v_extractionResult_5219_: *mut leanh::LeanObject,
    mut v_id_5220_: *mut leanh::LeanObject,
    mut v_projs_5221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5222_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(
        v_env_5215_,
        v_opts_5216_,
        v_ns_5217_,
        v_openDecls_5218_,
        v_extractionResult_5219_,
        v_id_5220_,
        v_projs_5221_,
    );
    leanh::lean_dec_ref(v_extractionResult_5219_);
    leanh::lean_dec_ref(v_opts_5216_);
    return v_res_5222_;
}
pub unsafe fn l_Lean_ResolveName_resolveGlobalName(
    mut v_env_5223_: *mut leanh::LeanObject,
    mut v_opts_5224_: *mut leanh::LeanObject,
    mut v_ns_5225_: *mut leanh::LeanObject,
    mut v_openDecls_5226_: *mut leanh::LeanObject,
    mut v_id_5227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_extractionResult_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_5229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_extractionResult_5228_ = l_Lean_extractMacroScopes(v_id_5227_);
    v_name_5229_ = leanh::lean_ctor_get(v_extractionResult_5228_, 0);
    leanh::lean_inc(v_name_5229_);
    v___x_5230_ = leanh::lean_box(0);
    v___x_5231_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(
        v_env_5223_,
        v_opts_5224_,
        v_ns_5225_,
        v_openDecls_5226_,
        v_extractionResult_5228_,
        v_name_5229_,
        v___x_5230_,
    );
    leanh::lean_dec_ref(v_extractionResult_5228_);
    return v___x_5231_;
}
pub unsafe fn l_Lean_ResolveName_resolveGlobalName___boxed(
    mut v_env_5232_: *mut leanh::LeanObject,
    mut v_opts_5233_: *mut leanh::LeanObject,
    mut v_ns_5234_: *mut leanh::LeanObject,
    mut v_openDecls_5235_: *mut leanh::LeanObject,
    mut v_id_5236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5237_ = l_Lean_ResolveName_resolveGlobalName(
        v_env_5232_,
        v_opts_5233_,
        v_ns_5234_,
        v_openDecls_5235_,
        v_id_5236_,
    );
    leanh::lean_dec_ref(v_opts_5233_);
    return v_res_5237_;
}
pub unsafe fn l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(
    mut v_msg_5238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5239_ = leanh::lean_box(0);
    v___x_5240_ = lean_panic_fn_borrowed(v___x_5239_, v_msg_5238_);
    return v___x_5240_;
}
pub unsafe fn _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5244_ = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2;
    v___x_5245_ = leanh::lean_unsigned_to_nat(9);
    v___x_5246_ = leanh::lean_unsigned_to_nat(230);
    v___x_5247_ = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1;
    v___x_5248_ = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0;
    v___x_5249_ = l_mkPanicMessageWithDecl(
        v___x_5248_,
        v___x_5247_,
        v___x_5246_,
        v___x_5245_,
        v___x_5244_,
    );
    return v___x_5249_;
}
pub unsafe fn l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(
    mut v_env_5250_: *mut leanh::LeanObject,
    mut v_n_5251_: *mut leanh::LeanObject,
    mut v_ns_5252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pre_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: u8 = 0;
    let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: u8 = 0;
    let mut v___x_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match leanh::lean_obj_tag(v_ns_5252_) {
                    1 => {
                        v_pre_5253_ = leanh::lean_ctor_get(v_ns_5252_, 0);
                        leanh::lean_inc(v_pre_5253_);
                        leanh::lean_inc(v_n_5251_);
                        v___x_5254_ = l_Lean_Name_append(v_ns_5252_, v_n_5251_);
                        leanh::lean_inc_ref(v_env_5250_);
                        v___x_5255_ = l_Lean_Environment_isNamespace(v_env_5250_, v___x_5254_);
                        if v___x_5255_ == 0 {
                            leanh::lean_dec(v___x_5254_);
                            v_ns_5252_ = v_pre_5253_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_pre_5253_);
                            leanh::lean_dec(v_n_5251_);
                            leanh::lean_dec_ref(v_env_5250_);
                            v___x_5257_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_5257_, 0, v___x_5254_);
                            return v___x_5257_;
                        }
                    }
                    0 => {
                        v___x_5258_ = l_Lean_rootNamespace;
                        v_n_5259_ = l_Lean_Name_replacePrefix(v_n_5251_, v___x_5258_, v_ns_5252_);
                        v___x_5260_ = l_Lean_Environment_isNamespace(v_env_5250_, v_n_5259_);
                        if v___x_5260_ == 0 {
                            leanh::lean_dec(v_n_5259_);
                            v___x_5261_ = leanh::lean_box(0);
                            return v___x_5261_;
                        } else {
                            v___x_5262_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_5262_, 0, v_n_5259_);
                            return v___x_5262_;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v_ns_5252_);
                        leanh::lean_dec(v_n_5251_);
                        leanh::lean_dec_ref(v_env_5250_);
                        v___x_5263_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3_once
                            ),
                            _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3,
                        );
                        v___x_5264_ = l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(v___x_5263_);
                        return v___x_5264_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(
    mut v_env_5265_: *mut leanh::LeanObject,
    mut v_n_5266_: *mut leanh::LeanObject,
    mut v_x_5267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5273_: u8 = 0;
    let mut v_ns_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_except_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5278_: u8 = 0;
    let mut v___x_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: u8 = 0;
    let mut v___x_5285_: u8 = 0;
    let mut v_isSharedCheck_5287_: u8 = 0;
    let mut v_unused_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5267_) == 0 {
                    leanh::lean_dec(v_n_5266_);
                    leanh::lean_dec_ref(v_env_5265_);
                    v___x_5268_ = leanh::lean_box(0);
                    return v___x_5268_;
                } else {
                    v_head_5269_ = leanh::lean_ctor_get(v_x_5267_, 0);
                    if leanh::lean_obj_tag(v_head_5269_) == 0 {
                        leanh::lean_inc_ref(v_head_5269_);
                        v_tail_5270_ = leanh::lean_ctor_get(v_x_5267_, 1);
                        v_isSharedCheck_5287_ = (!leanh::lean_is_exclusive(v_x_5267_)) as u8;
                        if v_isSharedCheck_5287_ == 0 {
                            v_unused_5288_ = leanh::lean_ctor_get(v_x_5267_, 0);
                            leanh::lean_dec(v_unused_5288_);
                            v___x_5272_ = v_x_5267_;
                            v_isShared_5273_ = v_isSharedCheck_5287_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_tail_5270_);
                            leanh::lean_dec(v_x_5267_);
                            v___x_5272_ = leanh::lean_box(0);
                            v_isShared_5273_ = v_isSharedCheck_5287_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_tail_5289_ = leanh::lean_ctor_get(v_x_5267_, 1);
                        leanh::lean_inc(v_tail_5289_);
                        leanh::lean_dec_ref_known(v_x_5267_, 2);
                        v_x_5267_ = v_tail_5289_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v_ns_5274_ = leanh::lean_ctor_get(v_head_5269_, 0);
                leanh::lean_inc(v_ns_5274_);
                v_except_5275_ = leanh::lean_ctor_get(v_head_5269_, 1);
                leanh::lean_inc(v_except_5275_);
                leanh::lean_dec_ref_known(v_head_5269_, 2);
                leanh::lean_inc(v_n_5266_);
                v___x_5276_ = l_Lean_Name_append(v_ns_5274_, v_n_5266_);
                leanh::lean_inc_ref(v_env_5265_);
                v___x_5284_ = l_Lean_Environment_isNamespace(v_env_5265_, v___x_5276_);
                if v___x_5284_ == 0 {
                    leanh::lean_dec(v_except_5275_);
                    v___y_5278_ = v___x_5284_;
                    state = 2;
                    continue;
                } else {
                    v___x_5285_ =
                        l_List_elem___at___00Lean_addAliasEntry_spec__2(v_n_5266_, v_except_5275_);
                    leanh::lean_dec(v_except_5275_);
                    if v___x_5285_ == 0 {
                        v___y_5278_ = v___x_5284_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5276_);
                        leanh::lean_del_object(v___x_5272_);
                        v_x_5267_ = v_tail_5270_;
                        state = 0;
                        continue;
                    }
                }
            }
            2 => {
                if v___y_5278_ == 0 {
                    leanh::lean_dec(v___x_5276_);
                    leanh::lean_del_object(v___x_5272_);
                    v_x_5267_ = v_tail_5270_;
                    state = 0;
                    continue;
                } else {
                    v___x_5280_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(
                        v_env_5265_,
                        v_n_5266_,
                        v_tail_5270_,
                    );
                    if v_isShared_5273_ == 0 {
                        leanh::lean_ctor_set(v___x_5272_, 1, v___x_5280_);
                        leanh::lean_ctor_set(v___x_5272_, 0, v___x_5276_);
                        v___x_5282_ = v___x_5272_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5283_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5283_, 0, v___x_5276_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5283_, 1, v___x_5280_);
                        v___x_5282_ = v_reuseFailAlloc_5283_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ResolveName_resolveNamespace(
    mut v_env_5291_: *mut leanh::LeanObject,
    mut v_ns_5292_: *mut leanh::LeanObject,
    mut v_openDecls_5293_: *mut leanh::LeanObject,
    mut v_id_5294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_id_5294_);
    leanh::lean_inc_ref(v_env_5291_);
    v___x_5295_ =
        l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(v_env_5291_, v_id_5294_, v_ns_5292_);
    if leanh::lean_obj_tag(v___x_5295_) == 0 {
        let mut v___x_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5296_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(
            v_env_5291_,
            v_id_5294_,
            v_openDecls_5293_,
        );
        return v___x_5296_;
    } else {
        let mut v_val_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5297_ = leanh::lean_ctor_get(v___x_5295_, 0);
        leanh::lean_inc(v_val_5297_);
        leanh::lean_dec_ref_known(v___x_5295_, 1);
        v___x_5298_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(
            v_env_5291_,
            v_id_5294_,
            v_openDecls_5293_,
        );
        v___x_5299_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5299_, 0, v_val_5297_);
        leanh::lean_ctor_set(v___x_5299_, 1, v___x_5298_);
        return v___x_5299_;
    }
}
pub unsafe fn l_Lean_instMonadResolveNameOfMonadLift___redArg(
    mut v_inst_5300_: *mut leanh::LeanObject,
    mut v_inst_5301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getCurrNamespace_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getOpenDecls_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5306_: u8 = 0;
    let mut v___x_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5312_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getCurrNamespace_5302_ = leanh::lean_ctor_get(v_inst_5301_, 0);
                v_getOpenDecls_5303_ = leanh::lean_ctor_get(v_inst_5301_, 1);
                v_isSharedCheck_5312_ = (!leanh::lean_is_exclusive(v_inst_5301_)) as u8;
                if v_isSharedCheck_5312_ == 0 {
                    v___x_5305_ = v_inst_5301_;
                    v_isShared_5306_ = v_isSharedCheck_5312_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_getOpenDecls_5303_);
                    leanh::lean_inc(v_getCurrNamespace_5302_);
                    leanh::lean_dec(v_inst_5301_);
                    v___x_5305_ = leanh::lean_box(0);
                    v_isShared_5306_ = v_isSharedCheck_5312_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_inst_5300_);
                v___x_5307_ = leanh::lean_apply_2(
                    v_inst_5300_,
                    leanh::lean_box(0),
                    v_getCurrNamespace_5302_,
                );
                v___x_5308_ = leanh::lean_apply_2(
                    v_inst_5300_,
                    leanh::lean_box(0),
                    v_getOpenDecls_5303_,
                );
                if v_isShared_5306_ == 0 {
                    leanh::lean_ctor_set(v___x_5305_, 1, v___x_5308_);
                    leanh::lean_ctor_set(v___x_5305_, 0, v___x_5307_);
                    v___x_5310_ = v___x_5305_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5311_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5311_, 0, v___x_5307_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5311_, 1, v___x_5308_);
                    v___x_5310_ = v_reuseFailAlloc_5311_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5310_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instMonadResolveNameOfMonadLift(
    mut v_m_5313_: *mut leanh::LeanObject,
    mut v_n_5314_: *mut leanh::LeanObject,
    mut v_inst_5315_: *mut leanh::LeanObject,
    mut v_inst_5316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5317_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v_inst_5315_, v_inst_5316_);
    return v___x_5317_;
}
pub unsafe fn _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5319_ = l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0;
    v___x_5320_ = l_Lean_stringToMessageData(v___x_5319_);
    return v___x_5320_;
}
pub unsafe fn _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5322_ = l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2;
    v___x_5323_ = l_Lean_stringToMessageData(v___x_5322_);
    return v___x_5323_;
}
pub unsafe fn l_Lean_checkPrivateInPublic___redArg___lam__0(
    mut v_____do__lift_5324_: *mut leanh::LeanObject,
    mut v_toApplicative_5325_: *mut leanh::LeanObject,
    mut v_id_5326_: *mut leanh::LeanObject,
    mut v_inst_5327_: *mut leanh::LeanObject,
    mut v_inst_5328_: *mut leanh::LeanObject,
    mut v_inst_5329_: *mut leanh::LeanObject,
    mut v_inst_5330_: *mut leanh::LeanObject,
    mut v_____do__lift_5331_: u8,
) -> *mut leanh::LeanObject {
    let mut v_toPure_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_5336_: u8 = 0;
    let mut v___x_5337_: u8 = 0;
    let mut v___x_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: u8 = 0;
    let mut v___x_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isExporting_5336_ = leanh::lean_ctor_get_uint8(
                    v_____do__lift_5324_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                if v_isExporting_5336_ == 0 {
                    leanh::lean_dec(v_inst_5330_);
                    leanh::lean_dec(v_inst_5329_);
                    leanh::lean_dec_ref(v_inst_5328_);
                    leanh::lean_dec_ref(v_inst_5327_);
                    leanh::lean_dec(v_id_5326_);
                    state = 1;
                    continue;
                } else {
                    v___x_5337_ = l_Lean_isPrivateName(v_id_5326_);
                    if v___x_5337_ == 0 {
                        leanh::lean_dec(v_inst_5330_);
                        leanh::lean_dec(v_inst_5329_);
                        leanh::lean_dec_ref(v_inst_5328_);
                        leanh::lean_dec_ref(v_inst_5327_);
                        leanh::lean_dec(v_id_5326_);
                        state = 1;
                        continue;
                    } else {
                        if v_____do__lift_5331_ == 0 {
                            leanh::lean_dec(v_inst_5330_);
                            leanh::lean_dec(v_inst_5329_);
                            leanh::lean_dec_ref(v_inst_5328_);
                            leanh::lean_dec_ref(v_inst_5327_);
                            leanh::lean_dec(v_id_5326_);
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_toApplicative_5325_);
                            v___x_5338_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1_once
                                ),
                                _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1,
                            );
                            v___x_5339_ = 0;
                            v___x_5340_ = l_Lean_MessageData_ofConstName(v_id_5326_, v___x_5339_);
                            v___x_5341_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5341_, 0, v___x_5338_);
                            leanh::lean_ctor_set(v___x_5341_, 1, v___x_5340_);
                            v___x_5342_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3_once
                                ),
                                _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3,
                            );
                            v___x_5343_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5343_, 0, v___x_5341_);
                            leanh::lean_ctor_set(v___x_5343_, 1, v___x_5342_);
                            v___x_5344_ = l_Lean_logWarning___redArg(
                                v_inst_5327_,
                                v_inst_5328_,
                                v_inst_5329_,
                                v_inst_5330_,
                                v___x_5343_,
                            );
                            return v___x_5344_;
                        }
                    }
                }
            }
            1 => {
                v_toPure_5333_ = leanh::lean_ctor_get(v_toApplicative_5325_, 1);
                leanh::lean_inc(v_toPure_5333_);
                leanh::lean_dec_ref(v_toApplicative_5325_);
                v___x_5334_ = leanh::lean_box(0);
                v___x_5335_ = leanh::lean_apply_2(
                    v_toPure_5333_,
                    leanh::lean_box(0),
                    v___x_5334_,
                );
                return v___x_5335_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_checkPrivateInPublic___redArg___lam__0___boxed(
    mut v_____do__lift_5345_: *mut leanh::LeanObject,
    mut v_toApplicative_5346_: *mut leanh::LeanObject,
    mut v_id_5347_: *mut leanh::LeanObject,
    mut v_inst_5348_: *mut leanh::LeanObject,
    mut v_inst_5349_: *mut leanh::LeanObject,
    mut v_inst_5350_: *mut leanh::LeanObject,
    mut v_inst_5351_: *mut leanh::LeanObject,
    mut v_____do__lift_5352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_231__boxed_5353_: u8 = 0;
    let mut v_res_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_231__boxed_5353_ = (leanh::lean_unbox(v_____do__lift_5352_) as u8);
    v_res_5354_ = l_Lean_checkPrivateInPublic___redArg___lam__0(
        v_____do__lift_5345_,
        v_toApplicative_5346_,
        v_id_5347_,
        v_inst_5348_,
        v_inst_5349_,
        v_inst_5350_,
        v_inst_5351_,
        v_____do__lift_231__boxed_5353_,
    );
    leanh::lean_dec_ref(v_____do__lift_5345_);
    return v_res_5354_;
}
pub unsafe fn l_Lean_checkPrivateInPublic___redArg___lam__1(
    mut v_toApplicative_5355_: *mut leanh::LeanObject,
    mut v_id_5356_: *mut leanh::LeanObject,
    mut v_inst_5357_: *mut leanh::LeanObject,
    mut v_inst_5358_: *mut leanh::LeanObject,
    mut v_inst_5359_: *mut leanh::LeanObject,
    mut v_inst_5360_: *mut leanh::LeanObject,
    mut v___x_5361_: *mut leanh::LeanObject,
    mut v_toBind_5362_: *mut leanh::LeanObject,
    mut v_____do__lift_5363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_inst_5360_);
    leanh::lean_inc_ref(v_inst_5357_);
    v___f_5364_ = leanh::lean_alloc_closure(
        l_Lean_checkPrivateInPublic___redArg___lam__0___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_5364_, 0, v_____do__lift_5363_);
    leanh::lean_closure_set(v___f_5364_, 1, v_toApplicative_5355_);
    leanh::lean_closure_set(v___f_5364_, 2, v_id_5356_);
    leanh::lean_closure_set(v___f_5364_, 3, v_inst_5357_);
    leanh::lean_closure_set(v___f_5364_, 4, v_inst_5358_);
    leanh::lean_closure_set(v___f_5364_, 5, v_inst_5359_);
    leanh::lean_closure_set(v___f_5364_, 6, v_inst_5360_);
    v___x_5365_ = l_Lean_ResolveName_backward_privateInPublic_warn;
    v___x_5366_ = l_Lean_Option_getM___redArg(v_inst_5357_, v_inst_5360_, v___x_5361_, v___x_5365_);
    v___x_5367_ = leanh::lean_apply_4(
        v_toBind_5362_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5366_,
        v___f_5364_,
    );
    return v___x_5367_;
}
pub unsafe fn l_Lean_checkPrivateInPublic___redArg(
    mut v_inst_5368_: *mut leanh::LeanObject,
    mut v_inst_5369_: *mut leanh::LeanObject,
    mut v_inst_5370_: *mut leanh::LeanObject,
    mut v_inst_5371_: *mut leanh::LeanObject,
    mut v_inst_5372_: *mut leanh::LeanObject,
    mut v_id_5373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5374_ = l_Lean_KVMap_instValueBool;
    v_toApplicative_5375_ = leanh::lean_ctor_get(v_inst_5368_, 0);
    leanh::lean_inc_ref(v_toApplicative_5375_);
    v_toBind_5376_ = leanh::lean_ctor_get(v_inst_5368_, 1);
    leanh::lean_inc_n(v_toBind_5376_, 2);
    v_getEnv_5377_ = leanh::lean_ctor_get(v_inst_5369_, 0);
    leanh::lean_inc(v_getEnv_5377_);
    leanh::lean_dec_ref(v_inst_5369_);
    v___f_5378_ = leanh::lean_alloc_closure(
        l_Lean_checkPrivateInPublic___redArg___lam__1 as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_5378_, 0, v_toApplicative_5375_);
    leanh::lean_closure_set(v___f_5378_, 1, v_id_5373_);
    leanh::lean_closure_set(v___f_5378_, 2, v_inst_5368_);
    leanh::lean_closure_set(v___f_5378_, 3, v_inst_5371_);
    leanh::lean_closure_set(v___f_5378_, 4, v_inst_5372_);
    leanh::lean_closure_set(v___f_5378_, 5, v_inst_5370_);
    leanh::lean_closure_set(v___f_5378_, 6, v___x_5374_);
    leanh::lean_closure_set(v___f_5378_, 7, v_toBind_5376_);
    v___x_5379_ = leanh::lean_apply_4(
        v_toBind_5376_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_5377_,
        v___f_5378_,
    );
    return v___x_5379_;
}
pub unsafe fn l_Lean_checkPrivateInPublic(
    mut v_m_5380_: *mut leanh::LeanObject,
    mut v_inst_5381_: *mut leanh::LeanObject,
    mut v_inst_5382_: *mut leanh::LeanObject,
    mut v_inst_5383_: *mut leanh::LeanObject,
    mut v_inst_5384_: *mut leanh::LeanObject,
    mut v_inst_5385_: *mut leanh::LeanObject,
    mut v_id_5386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5387_ = l_Lean_checkPrivateInPublic___redArg(
        v_inst_5381_,
        v_inst_5382_,
        v_inst_5383_,
        v_inst_5384_,
        v_inst_5385_,
        v_id_5386_,
    );
    return v___x_5387_;
}
pub unsafe fn l_Lean_isInaccessiblePrivateName___redArg___lam__0(
    mut v_env_5388_: *mut leanh::LeanObject,
    mut v_n_5389_: *mut leanh::LeanObject,
    mut v_toApplicative_5390_: *mut leanh::LeanObject,
    mut v___y_5391_: u8,
    mut v___x_5392_: u8,
    mut v_____r_5393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5394_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_5388_, v_n_5389_);
    if leanh::lean_obj_tag(v___x_5394_) == 0 {
        let mut v_toPure_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5397_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toPure_5395_ = leanh::lean_ctor_get(v_toApplicative_5390_, 1);
        leanh::lean_inc(v_toPure_5395_);
        leanh::lean_dec_ref(v_toApplicative_5390_);
        v___x_5396_ = leanh::lean_box((v___y_5391_) as usize);
        v___x_5397_ =
            leanh::lean_apply_2(v_toPure_5395_, leanh::lean_box(0), v___x_5396_);
        return v___x_5397_;
    } else {
        let mut v_val_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5400_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isModule_5401_: u8 = 0;
        v_val_5398_ = leanh::lean_ctor_get(v___x_5394_, 0);
        leanh::lean_inc(v_val_5398_);
        leanh::lean_dec_ref_known(v___x_5394_, 1);
        v_toPure_5399_ = leanh::lean_ctor_get(v_toApplicative_5390_, 1);
        leanh::lean_inc(v_toPure_5399_);
        leanh::lean_dec_ref(v_toApplicative_5390_);
        v___x_5400_ = l_Lean_Environment_header(v_env_5388_);
        v_isModule_5401_ = leanh::lean_ctor_get_uint8(
            v___x_5400_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 4) as u32,
        );
        if v_isModule_5401_ == 0 {
            let mut v___x_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___x_5400_);
            leanh::lean_dec(v_val_5398_);
            v___x_5402_ = leanh::lean_box((v___x_5392_) as usize);
            v___x_5403_ =
                leanh::lean_apply_2(v_toPure_5399_, leanh::lean_box(0), v___x_5402_);
            return v___x_5403_;
        } else {
            let mut v_modules_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5406_: u8 = 0;
            v_modules_5404_ = leanh::lean_ctor_get(v___x_5400_, 3);
            leanh::lean_inc_ref(v_modules_5404_);
            leanh::lean_dec_ref(v___x_5400_);
            v___x_5405_ = lean_array_get_size(v_modules_5404_);
            v___x_5406_ = lean_nat_dec_lt(v_val_5398_, v___x_5405_);
            if v___x_5406_ == 0 {
                let mut v___x_5407_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5408_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_modules_5404_);
                leanh::lean_dec(v_val_5398_);
                v___x_5407_ = leanh::lean_box((v_isModule_5401_) as usize);
                v___x_5408_ = leanh::lean_apply_2(
                    v_toPure_5399_,
                    leanh::lean_box(0),
                    v___x_5407_,
                );
                return v___x_5408_;
            } else {
                let mut v___x_5409_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_toImport_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_importAll_5411_: u8 = 0;
                v___x_5409_ = lean_array_fget(v_modules_5404_, v_val_5398_);
                leanh::lean_dec(v_val_5398_);
                leanh::lean_dec_ref(v_modules_5404_);
                v_toImport_5410_ = leanh::lean_ctor_get(v___x_5409_, 0);
                leanh::lean_inc_ref(v_toImport_5410_);
                leanh::lean_dec(v___x_5409_);
                v_importAll_5411_ = leanh::lean_ctor_get_uint8(
                    v_toImport_5410_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                leanh::lean_dec_ref(v_toImport_5410_);
                if v_importAll_5411_ == 0 {
                    let mut v___x_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_5412_ = leanh::lean_box((v_isModule_5401_) as usize);
                    v___x_5413_ = leanh::lean_apply_2(
                        v_toPure_5399_,
                        leanh::lean_box(0),
                        v___x_5412_,
                    );
                    return v___x_5413_;
                } else {
                    let mut v___x_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_5414_ = leanh::lean_box((v___y_5391_) as usize);
                    v___x_5415_ = leanh::lean_apply_2(
                        v_toPure_5399_,
                        leanh::lean_box(0),
                        v___x_5414_,
                    );
                    return v___x_5415_;
                }
            }
        }
    }
}
pub unsafe fn l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed(
    mut v_env_5416_: *mut leanh::LeanObject,
    mut v_n_5417_: *mut leanh::LeanObject,
    mut v_toApplicative_5418_: *mut leanh::LeanObject,
    mut v___y_5419_: *mut leanh::LeanObject,
    mut v___x_5420_: *mut leanh::LeanObject,
    mut v_____r_5421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_758__boxed_5422_: u8 = 0;
    let mut v___x_759__boxed_5423_: u8 = 0;
    let mut v_res_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_758__boxed_5422_ = (leanh::lean_unbox(v___y_5419_) as u8);
    v___x_759__boxed_5423_ = (leanh::lean_unbox(v___x_5420_) as u8);
    v_res_5424_ = l_Lean_isInaccessiblePrivateName___redArg___lam__0(
        v_env_5416_,
        v_n_5417_,
        v_toApplicative_5418_,
        v___y_758__boxed_5422_,
        v___x_759__boxed_5423_,
        v_____r_5421_,
    );
    leanh::lean_dec(v_n_5417_);
    leanh::lean_dec_ref(v_env_5416_);
    return v_res_5424_;
}
pub unsafe fn l_Lean_isInaccessiblePrivateName___redArg___lam__1(
    mut v_env_5425_: *mut leanh::LeanObject,
    mut v_n_5426_: *mut leanh::LeanObject,
    mut v_toApplicative_5427_: *mut leanh::LeanObject,
    mut v___x_5428_: u8,
    mut v_inst_5429_: *mut leanh::LeanObject,
    mut v_inst_5430_: *mut leanh::LeanObject,
    mut v_inst_5431_: *mut leanh::LeanObject,
    mut v_inst_5432_: *mut leanh::LeanObject,
    mut v_inst_5433_: *mut leanh::LeanObject,
    mut v_toBind_5434_: *mut leanh::LeanObject,
    mut v___x_5435_: u8,
    mut v_____do__lift_5436_: u8,
) -> *mut leanh::LeanObject {
    let mut v___y_5438_: u8 = 0;
    let mut v___x_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_5444_: u8 = 0;
    let mut v_toPure_5445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isExporting_5444_ = leanh::lean_ctor_get_uint8(
                    v_env_5425_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                if v_isExporting_5444_ == 0 {
                    v___y_5438_ = v_isExporting_5444_;
                    state = 1;
                    continue;
                } else {
                    if v_____do__lift_5436_ == 0 {
                        leanh::lean_dec(v_toBind_5434_);
                        leanh::lean_dec(v_inst_5433_);
                        leanh::lean_dec_ref(v_inst_5432_);
                        leanh::lean_dec(v_inst_5431_);
                        leanh::lean_dec_ref(v_inst_5430_);
                        leanh::lean_dec_ref(v_inst_5429_);
                        leanh::lean_dec(v_n_5426_);
                        leanh::lean_dec_ref(v_env_5425_);
                        v_toPure_5445_ = leanh::lean_ctor_get(v_toApplicative_5427_, 1);
                        leanh::lean_inc(v_toPure_5445_);
                        leanh::lean_dec_ref(v_toApplicative_5427_);
                        v___x_5446_ = leanh::lean_box((v___x_5428_) as usize);
                        v___x_5447_ = leanh::lean_apply_2(
                            v_toPure_5445_,
                            leanh::lean_box(0),
                            v___x_5446_,
                        );
                        return v___x_5447_;
                    } else {
                        v___y_5438_ = v___x_5435_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5439_ = leanh::lean_box((v___y_5438_) as usize);
                v___x_5440_ = leanh::lean_box((v___x_5428_) as usize);
                leanh::lean_inc(v_n_5426_);
                v___f_5441_ = leanh::lean_alloc_closure(
                    l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    6,
                    5,
                );
                leanh::lean_closure_set(v___f_5441_, 0, v_env_5425_);
                leanh::lean_closure_set(v___f_5441_, 1, v_n_5426_);
                leanh::lean_closure_set(v___f_5441_, 2, v_toApplicative_5427_);
                leanh::lean_closure_set(v___f_5441_, 3, v___x_5439_);
                leanh::lean_closure_set(v___f_5441_, 4, v___x_5440_);
                v___x_5442_ = l_Lean_checkPrivateInPublic___redArg(
                    v_inst_5429_,
                    v_inst_5430_,
                    v_inst_5431_,
                    v_inst_5432_,
                    v_inst_5433_,
                    v_n_5426_,
                );
                v___x_5443_ = leanh::lean_apply_4(
                    v_toBind_5434_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_5442_,
                    v___f_5441_,
                );
                return v___x_5443_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed(
    mut v_env_5448_: *mut leanh::LeanObject,
    mut v_n_5449_: *mut leanh::LeanObject,
    mut v_toApplicative_5450_: *mut leanh::LeanObject,
    mut v___x_5451_: *mut leanh::LeanObject,
    mut v_inst_5452_: *mut leanh::LeanObject,
    mut v_inst_5453_: *mut leanh::LeanObject,
    mut v_inst_5454_: *mut leanh::LeanObject,
    mut v_inst_5455_: *mut leanh::LeanObject,
    mut v_inst_5456_: *mut leanh::LeanObject,
    mut v_toBind_5457_: *mut leanh::LeanObject,
    mut v___x_5458_: *mut leanh::LeanObject,
    mut v_____do__lift_5459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_799__boxed_5460_: u8 = 0;
    let mut v___x_805__boxed_5461_: u8 = 0;
    let mut v_____do__lift_806__boxed_5462_: u8 = 0;
    let mut v_res_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_799__boxed_5460_ = (leanh::lean_unbox(v___x_5451_) as u8);
    v___x_805__boxed_5461_ = (leanh::lean_unbox(v___x_5458_) as u8);
    v_____do__lift_806__boxed_5462_ = (leanh::lean_unbox(v_____do__lift_5459_) as u8);
    v_res_5463_ = l_Lean_isInaccessiblePrivateName___redArg___lam__1(
        v_env_5448_,
        v_n_5449_,
        v_toApplicative_5450_,
        v___x_799__boxed_5460_,
        v_inst_5452_,
        v_inst_5453_,
        v_inst_5454_,
        v_inst_5455_,
        v_inst_5456_,
        v_toBind_5457_,
        v___x_805__boxed_5461_,
        v_____do__lift_806__boxed_5462_,
    );
    return v_res_5463_;
}
pub unsafe fn l_Lean_isInaccessiblePrivateName___redArg___lam__2(
    mut v_n_5464_: *mut leanh::LeanObject,
    mut v_toApplicative_5465_: *mut leanh::LeanObject,
    mut v___x_5466_: u8,
    mut v_inst_5467_: *mut leanh::LeanObject,
    mut v_inst_5468_: *mut leanh::LeanObject,
    mut v_inst_5469_: *mut leanh::LeanObject,
    mut v_inst_5470_: *mut leanh::LeanObject,
    mut v_inst_5471_: *mut leanh::LeanObject,
    mut v_toBind_5472_: *mut leanh::LeanObject,
    mut v___x_5473_: u8,
    mut v_env_5474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5475_ = leanh::lean_box((v___x_5466_) as usize);
    v___x_5476_ = leanh::lean_box((v___x_5473_) as usize);
    leanh::lean_inc(v_toBind_5472_);
    leanh::lean_inc(v_inst_5469_);
    leanh::lean_inc_ref(v_inst_5467_);
    v___f_5477_ = leanh::lean_alloc_closure(
        l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    leanh::lean_closure_set(v___f_5477_, 0, v_env_5474_);
    leanh::lean_closure_set(v___f_5477_, 1, v_n_5464_);
    leanh::lean_closure_set(v___f_5477_, 2, v_toApplicative_5465_);
    leanh::lean_closure_set(v___f_5477_, 3, v___x_5475_);
    leanh::lean_closure_set(v___f_5477_, 4, v_inst_5467_);
    leanh::lean_closure_set(v___f_5477_, 5, v_inst_5468_);
    leanh::lean_closure_set(v___f_5477_, 6, v_inst_5469_);
    leanh::lean_closure_set(v___f_5477_, 7, v_inst_5470_);
    leanh::lean_closure_set(v___f_5477_, 8, v_inst_5471_);
    leanh::lean_closure_set(v___f_5477_, 9, v_toBind_5472_);
    leanh::lean_closure_set(v___f_5477_, 10, v___x_5476_);
    v___x_5478_ = l_Lean_KVMap_instValueBool;
    v___x_5479_ = l_Lean_ResolveName_backward_privateInPublic;
    v___x_5480_ = l_Lean_Option_getM___redArg(v_inst_5467_, v_inst_5469_, v___x_5478_, v___x_5479_);
    v___x_5481_ = leanh::lean_apply_4(
        v_toBind_5472_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5480_,
        v___f_5477_,
    );
    return v___x_5481_;
}
pub unsafe fn l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed(
    mut v_n_5482_: *mut leanh::LeanObject,
    mut v_toApplicative_5483_: *mut leanh::LeanObject,
    mut v___x_5484_: *mut leanh::LeanObject,
    mut v_inst_5485_: *mut leanh::LeanObject,
    mut v_inst_5486_: *mut leanh::LeanObject,
    mut v_inst_5487_: *mut leanh::LeanObject,
    mut v_inst_5488_: *mut leanh::LeanObject,
    mut v_inst_5489_: *mut leanh::LeanObject,
    mut v_toBind_5490_: *mut leanh::LeanObject,
    mut v___x_5491_: *mut leanh::LeanObject,
    mut v_env_5492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_841__boxed_5493_: u8 = 0;
    let mut v___x_847__boxed_5494_: u8 = 0;
    let mut v_res_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_841__boxed_5493_ = (leanh::lean_unbox(v___x_5484_) as u8);
    v___x_847__boxed_5494_ = (leanh::lean_unbox(v___x_5491_) as u8);
    v_res_5495_ = l_Lean_isInaccessiblePrivateName___redArg___lam__2(
        v_n_5482_,
        v_toApplicative_5483_,
        v___x_841__boxed_5493_,
        v_inst_5485_,
        v_inst_5486_,
        v_inst_5487_,
        v_inst_5488_,
        v_inst_5489_,
        v_toBind_5490_,
        v___x_847__boxed_5494_,
        v_env_5492_,
    );
    return v_res_5495_;
}
pub unsafe fn l_Lean_isInaccessiblePrivateName___redArg(
    mut v_inst_5496_: *mut leanh::LeanObject,
    mut v_inst_5497_: *mut leanh::LeanObject,
    mut v_inst_5498_: *mut leanh::LeanObject,
    mut v_inst_5499_: *mut leanh::LeanObject,
    mut v_inst_5500_: *mut leanh::LeanObject,
    mut v_n_5501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5502_: u8 = 0;
    v___x_5502_ = l_Lean_isPrivateName(v_n_5501_);
    if v___x_5502_ == 0 {
        let mut v_toApplicative_5503_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_5504_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_n_5501_);
        leanh::lean_dec(v_inst_5500_);
        leanh::lean_dec_ref(v_inst_5499_);
        leanh::lean_dec(v_inst_5497_);
        leanh::lean_dec_ref(v_inst_5496_);
        v_toApplicative_5503_ = leanh::lean_ctor_get(v_inst_5498_, 0);
        leanh::lean_inc_ref(v_toApplicative_5503_);
        leanh::lean_dec_ref(v_inst_5498_);
        v_toPure_5504_ = leanh::lean_ctor_get(v_toApplicative_5503_, 1);
        leanh::lean_inc(v_toPure_5504_);
        leanh::lean_dec_ref(v_toApplicative_5503_);
        v___x_5505_ = leanh::lean_box((v___x_5502_) as usize);
        v___x_5506_ =
            leanh::lean_apply_2(v_toPure_5504_, leanh::lean_box(0), v___x_5505_);
        return v___x_5506_;
    } else {
        let mut v_toApplicative_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5510_: u8 = 0;
        let mut v___x_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_5507_ = leanh::lean_ctor_get(v_inst_5498_, 0);
        leanh::lean_inc_ref(v_toApplicative_5507_);
        v_toBind_5508_ = leanh::lean_ctor_get(v_inst_5498_, 1);
        leanh::lean_inc_n(v_toBind_5508_, 2);
        v_getEnv_5509_ = leanh::lean_ctor_get(v_inst_5499_, 0);
        leanh::lean_inc(v_getEnv_5509_);
        v___x_5510_ = 0;
        v___x_5511_ = leanh::lean_box((v___x_5502_) as usize);
        v___x_5512_ = leanh::lean_box((v___x_5510_) as usize);
        v___f_5513_ = leanh::lean_alloc_closure(
            l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed as *mut core::ffi::c_void,
            11,
            10,
        );
        leanh::lean_closure_set(v___f_5513_, 0, v_n_5501_);
        leanh::lean_closure_set(v___f_5513_, 1, v_toApplicative_5507_);
        leanh::lean_closure_set(v___f_5513_, 2, v___x_5511_);
        leanh::lean_closure_set(v___f_5513_, 3, v_inst_5498_);
        leanh::lean_closure_set(v___f_5513_, 4, v_inst_5499_);
        leanh::lean_closure_set(v___f_5513_, 5, v_inst_5500_);
        leanh::lean_closure_set(v___f_5513_, 6, v_inst_5496_);
        leanh::lean_closure_set(v___f_5513_, 7, v_inst_5497_);
        leanh::lean_closure_set(v___f_5513_, 8, v_toBind_5508_);
        leanh::lean_closure_set(v___f_5513_, 9, v___x_5512_);
        v___x_5514_ = leanh::lean_apply_4(
            v_toBind_5508_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_5509_,
            v___f_5513_,
        );
        return v___x_5514_;
    }
}
pub unsafe fn l_Lean_isInaccessiblePrivateName(
    mut v_m_5515_: *mut leanh::LeanObject,
    mut v_inst_5516_: *mut leanh::LeanObject,
    mut v_inst_5517_: *mut leanh::LeanObject,
    mut v_inst_5518_: *mut leanh::LeanObject,
    mut v_inst_5519_: *mut leanh::LeanObject,
    mut v_inst_5520_: *mut leanh::LeanObject,
    mut v_n_5521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5522_ = l_Lean_isInaccessiblePrivateName___redArg(
        v_inst_5516_,
        v_inst_5517_,
        v_inst_5518_,
        v_inst_5519_,
        v_inst_5520_,
        v_n_5521_,
    );
    return v___x_5522_;
}
pub unsafe fn l_Lean_resolveGlobalName___redArg___lam__0(
    mut v_x_5523_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: u8 = 0;
    v_fst_5524_ = leanh::lean_ctor_get(v_x_5523_, 0);
    v___x_5525_ = l_Lean_isPrivateName(v_fst_5524_);
    return v___x_5525_;
}
pub unsafe fn l_Lean_resolveGlobalName___redArg___lam__0___boxed(
    mut v_x_5526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5527_: u8 = 0;
    let mut v_r_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5527_ = l_Lean_resolveGlobalName___redArg___lam__0(v_x_5526_);
    leanh::lean_dec_ref(v_x_5526_);
    v_r_5528_ = leanh::lean_box((v_res_5527_) as usize);
    return v_r_5528_;
}
pub unsafe fn l_Lean_resolveGlobalName___redArg___lam__1(
    mut v_toPure_5529_: *mut leanh::LeanObject,
    mut v_res_5530_: *mut leanh::LeanObject,
    mut v_____r_5531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5532_ =
        leanh::lean_apply_2(v_toPure_5529_, leanh::lean_box(0), v_res_5530_);
    return v___x_5532_;
}
pub unsafe fn l_Lean_resolveGlobalName___redArg___lam__2(
    mut v_enableLog_5533_: u8,
    mut v_toPure_5534_: *mut leanh::LeanObject,
    mut v_res_5535_: *mut leanh::LeanObject,
    mut v___f_5536_: *mut leanh::LeanObject,
    mut v_inst_5537_: *mut leanh::LeanObject,
    mut v_inst_5538_: *mut leanh::LeanObject,
    mut v_inst_5539_: *mut leanh::LeanObject,
    mut v_inst_5540_: *mut leanh::LeanObject,
    mut v_inst_5541_: *mut leanh::LeanObject,
    mut v_toBind_5542_: *mut leanh::LeanObject,
    mut v___f_5543_: *mut leanh::LeanObject,
    mut v_____do__lift_5544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_enableLog_5533_ == 0 {
        let mut v___x_5545_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_5543_);
        leanh::lean_dec(v_toBind_5542_);
        leanh::lean_dec(v_inst_5541_);
        leanh::lean_dec_ref(v_inst_5540_);
        leanh::lean_dec(v_inst_5539_);
        leanh::lean_dec_ref(v_inst_5538_);
        leanh::lean_dec_ref(v_inst_5537_);
        leanh::lean_dec_ref(v___f_5536_);
        v___x_5545_ =
            leanh::lean_apply_2(v_toPure_5534_, leanh::lean_box(0), v_res_5535_);
        return v___x_5545_;
    } else {
        let mut v_isExporting_5546_: u8 = 0;
        v_isExporting_5546_ = leanh::lean_ctor_get_uint8(
            v_____do__lift_5544_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
        );
        if v_isExporting_5546_ == 0 {
            let mut v___x_5547_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___f_5543_);
            leanh::lean_dec(v_toBind_5542_);
            leanh::lean_dec(v_inst_5541_);
            leanh::lean_dec_ref(v_inst_5540_);
            leanh::lean_dec(v_inst_5539_);
            leanh::lean_dec_ref(v_inst_5538_);
            leanh::lean_dec_ref(v_inst_5537_);
            leanh::lean_dec_ref(v___f_5536_);
            v___x_5547_ =
                leanh::lean_apply_2(v_toPure_5534_, leanh::lean_box(0), v_res_5535_);
            return v___x_5547_;
        } else {
            let mut v___x_5548_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_res_5535_);
            v___x_5548_ = l_List_find_x3f___redArg(v___f_5536_, v_res_5535_);
            if leanh::lean_obj_tag(v___x_5548_) == 1 {
                let mut v_val_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_fst_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5551_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5552_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_res_5535_);
                leanh::lean_dec(v_toPure_5534_);
                v_val_5549_ = leanh::lean_ctor_get(v___x_5548_, 0);
                leanh::lean_inc(v_val_5549_);
                leanh::lean_dec_ref_known(v___x_5548_, 1);
                v_fst_5550_ = leanh::lean_ctor_get(v_val_5549_, 0);
                leanh::lean_inc(v_fst_5550_);
                leanh::lean_dec(v_val_5549_);
                v___x_5551_ = l_Lean_checkPrivateInPublic___redArg(
                    v_inst_5537_,
                    v_inst_5538_,
                    v_inst_5539_,
                    v_inst_5540_,
                    v_inst_5541_,
                    v_fst_5550_,
                );
                v___x_5552_ = leanh::lean_apply_4(
                    v_toBind_5542_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_5551_,
                    v___f_5543_,
                );
                return v___x_5552_;
            } else {
                let mut v___x_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_5548_);
                leanh::lean_dec(v___f_5543_);
                leanh::lean_dec(v_toBind_5542_);
                leanh::lean_dec(v_inst_5541_);
                leanh::lean_dec_ref(v_inst_5540_);
                leanh::lean_dec(v_inst_5539_);
                leanh::lean_dec_ref(v_inst_5538_);
                leanh::lean_dec_ref(v_inst_5537_);
                v___x_5553_ = leanh::lean_apply_2(
                    v_toPure_5534_,
                    leanh::lean_box(0),
                    v_res_5535_,
                );
                return v___x_5553_;
            }
        }
    }
}
pub unsafe fn l_Lean_resolveGlobalName___redArg___lam__2___boxed(
    mut v_enableLog_5554_: *mut leanh::LeanObject,
    mut v_toPure_5555_: *mut leanh::LeanObject,
    mut v_res_5556_: *mut leanh::LeanObject,
    mut v___f_5557_: *mut leanh::LeanObject,
    mut v_inst_5558_: *mut leanh::LeanObject,
    mut v_inst_5559_: *mut leanh::LeanObject,
    mut v_inst_5560_: *mut leanh::LeanObject,
    mut v_inst_5561_: *mut leanh::LeanObject,
    mut v_inst_5562_: *mut leanh::LeanObject,
    mut v_toBind_5563_: *mut leanh::LeanObject,
    mut v___f_5564_: *mut leanh::LeanObject,
    mut v_____do__lift_5565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_enableLog_boxed_5566_: u8 = 0;
    let mut v_res_5567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_enableLog_boxed_5566_ = (leanh::lean_unbox(v_enableLog_5554_) as u8);
    v_res_5567_ = l_Lean_resolveGlobalName___redArg___lam__2(
        v_enableLog_boxed_5566_,
        v_toPure_5555_,
        v_res_5556_,
        v___f_5557_,
        v_inst_5558_,
        v_inst_5559_,
        v_inst_5560_,
        v_inst_5561_,
        v_inst_5562_,
        v_toBind_5563_,
        v___f_5564_,
        v_____do__lift_5565_,
    );
    leanh::lean_dec_ref(v_____do__lift_5565_);
    return v_res_5567_;
}
pub unsafe fn l_Lean_resolveGlobalName___redArg___lam__3(
    mut v_____do__lift_5568_: *mut leanh::LeanObject,
    mut v_____do__lift_5569_: *mut leanh::LeanObject,
    mut v_____do__lift_5570_: *mut leanh::LeanObject,
    mut v_id_5571_: *mut leanh::LeanObject,
    mut v_toPure_5572_: *mut leanh::LeanObject,
    mut v_enableLog_5573_: u8,
    mut v___f_5574_: *mut leanh::LeanObject,
    mut v_inst_5575_: *mut leanh::LeanObject,
    mut v_inst_5576_: *mut leanh::LeanObject,
    mut v_inst_5577_: *mut leanh::LeanObject,
    mut v_inst_5578_: *mut leanh::LeanObject,
    mut v_inst_5579_: *mut leanh::LeanObject,
    mut v_toBind_5580_: *mut leanh::LeanObject,
    mut v_getEnv_5581_: *mut leanh::LeanObject,
    mut v_____do__lift_5582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5583_ = l_Lean_ResolveName_resolveGlobalName(
        v_____do__lift_5568_,
        v_____do__lift_5569_,
        v_____do__lift_5570_,
        v_____do__lift_5582_,
        v_id_5571_,
    );
    leanh::lean_inc(v_res_5583_);
    leanh::lean_inc(v_toPure_5572_);
    v___f_5584_ = leanh::lean_alloc_closure(
        l_Lean_resolveGlobalName___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_5584_, 0, v_toPure_5572_);
    leanh::lean_closure_set(v___f_5584_, 1, v_res_5583_);
    v___x_5585_ = leanh::lean_box((v_enableLog_5573_) as usize);
    leanh::lean_inc(v_toBind_5580_);
    v___f_5586_ = leanh::lean_alloc_closure(
        l_Lean_resolveGlobalName___redArg___lam__2___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    leanh::lean_closure_set(v___f_5586_, 0, v___x_5585_);
    leanh::lean_closure_set(v___f_5586_, 1, v_toPure_5572_);
    leanh::lean_closure_set(v___f_5586_, 2, v_res_5583_);
    leanh::lean_closure_set(v___f_5586_, 3, v___f_5574_);
    leanh::lean_closure_set(v___f_5586_, 4, v_inst_5575_);
    leanh::lean_closure_set(v___f_5586_, 5, v_inst_5576_);
    leanh::lean_closure_set(v___f_5586_, 6, v_inst_5577_);
    leanh::lean_closure_set(v___f_5586_, 7, v_inst_5578_);
    leanh::lean_closure_set(v___f_5586_, 8, v_inst_5579_);
    leanh::lean_closure_set(v___f_5586_, 9, v_toBind_5580_);
    leanh::lean_closure_set(v___f_5586_, 10, v___f_5584_);
    v___x_5587_ = leanh::lean_apply_4(
        v_toBind_5580_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_5581_,
        v___f_5586_,
    );
    return v___x_5587_;
}
pub unsafe fn l_Lean_resolveGlobalName___redArg___lam__3___boxed(
    mut v_____do__lift_5588_: *mut leanh::LeanObject,
    mut v_____do__lift_5589_: *mut leanh::LeanObject,
    mut v_____do__lift_5590_: *mut leanh::LeanObject,
    mut v_id_5591_: *mut leanh::LeanObject,
    mut v_toPure_5592_: *mut leanh::LeanObject,
    mut v_enableLog_5593_: *mut leanh::LeanObject,
    mut v___f_5594_: *mut leanh::LeanObject,
    mut v_inst_5595_: *mut leanh::LeanObject,
    mut v_inst_5596_: *mut leanh::LeanObject,
    mut v_inst_5597_: *mut leanh::LeanObject,
    mut v_inst_5598_: *mut leanh::LeanObject,
    mut v_inst_5599_: *mut leanh::LeanObject,
    mut v_toBind_5600_: *mut leanh::LeanObject,
    mut v_getEnv_5601_: *mut leanh::LeanObject,
    mut v_____do__lift_5602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_enableLog_boxed_5603_: u8 = 0;
    let mut v_res_5604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_enableLog_boxed_5603_ = (leanh::lean_unbox(v_enableLog_5593_) as u8);
    v_res_5604_ = l_Lean_resolveGlobalName___redArg___lam__3(
        v_____do__lift_5588_,
        v_____do__lift_5589_,
        v_____do__lift_5590_,
        v_id_5591_,
        v_toPure_5592_,
        v_enableLog_boxed_5603_,
        v___f_5594_,
        v_inst_5595_,
        v_inst_5596_,
        v_inst_5597_,
        v_inst_5598_,
        v_inst_5599_,
        v_toBind_5600_,
        v_getEnv_5601_,
        v_____do__lift_5602_,
    );
    leanh::lean_dec_ref(v_____do__lift_5589_);
    return v_res_5604_;
}
pub unsafe fn l_Lean_resolveGlobalName___redArg___lam__4(
    mut v_____do__lift_5605_: *mut leanh::LeanObject,
    mut v_____do__lift_5606_: *mut leanh::LeanObject,
    mut v_id_5607_: *mut leanh::LeanObject,
    mut v_toPure_5608_: *mut leanh::LeanObject,
    mut v_enableLog_5609_: u8,
    mut v___f_5610_: *mut leanh::LeanObject,
    mut v_inst_5611_: *mut leanh::LeanObject,
    mut v_inst_5612_: *mut leanh::LeanObject,
    mut v_inst_5613_: *mut leanh::LeanObject,
    mut v_inst_5614_: *mut leanh::LeanObject,
    mut v_inst_5615_: *mut leanh::LeanObject,
    mut v_toBind_5616_: *mut leanh::LeanObject,
    mut v_getEnv_5617_: *mut leanh::LeanObject,
    mut v_getOpenDecls_5618_: *mut leanh::LeanObject,
    mut v_____do__lift_5619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5620_ = leanh::lean_box((v_enableLog_5609_) as usize);
    leanh::lean_inc(v_toBind_5616_);
    v___f_5621_ = leanh::lean_alloc_closure(
        l_Lean_resolveGlobalName___redArg___lam__3___boxed as *mut core::ffi::c_void,
        15,
        14,
    );
    leanh::lean_closure_set(v___f_5621_, 0, v_____do__lift_5605_);
    leanh::lean_closure_set(v___f_5621_, 1, v_____do__lift_5606_);
    leanh::lean_closure_set(v___f_5621_, 2, v_____do__lift_5619_);
    leanh::lean_closure_set(v___f_5621_, 3, v_id_5607_);
    leanh::lean_closure_set(v___f_5621_, 4, v_toPure_5608_);
    leanh::lean_closure_set(v___f_5621_, 5, v___x_5620_);
    leanh::lean_closure_set(v___f_5621_, 6, v___f_5610_);
    leanh::lean_closure_set(v___f_5621_, 7, v_inst_5611_);
    leanh::lean_closure_set(v___f_5621_, 8, v_inst_5612_);
    leanh::lean_closure_set(v___f_5621_, 9, v_inst_5613_);
    leanh::lean_closure_set(v___f_5621_, 10, v_inst_5614_);
    leanh::lean_closure_set(v___f_5621_, 11, v_inst_5615_);
    leanh::lean_closure_set(v___f_5621_, 12, v_toBind_5616_);
    leanh::lean_closure_set(v___f_5621_, 13, v_getEnv_5617_);
    v___x_5622_ = leanh::lean_apply_4(
        v_toBind_5616_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getOpenDecls_5618_,
        v___f_5621_,
    );
    return v___x_5622_;
}
pub unsafe fn l_Lean_resolveGlobalName___redArg___lam__4___boxed(
    mut v_____do__lift_5623_: *mut leanh::LeanObject,
    mut v_____do__lift_5624_: *mut leanh::LeanObject,
    mut v_id_5625_: *mut leanh::LeanObject,
    mut v_toPure_5626_: *mut leanh::LeanObject,
    mut v_enableLog_5627_: *mut leanh::LeanObject,
    mut v___f_5628_: *mut leanh::LeanObject,
    mut v_inst_5629_: *mut leanh::LeanObject,
    mut v_inst_5630_: *mut leanh::LeanObject,
    mut v_inst_5631_: *mut leanh::LeanObject,
    mut v_inst_5632_: *mut leanh::LeanObject,
    mut v_inst_5633_: *mut leanh::LeanObject,
    mut v_toBind_5634_: *mut leanh::LeanObject,
    mut v_getEnv_5635_: *mut leanh::LeanObject,
    mut v_getOpenDecls_5636_: *mut leanh::LeanObject,
    mut v_____do__lift_5637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_enableLog_boxed_5638_: u8 = 0;
    let mut v_res_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_enableLog_boxed_5638_ = (leanh::lean_unbox(v_enableLog_5627_) as u8);
    v_res_5639_ = l_Lean_resolveGlobalName___redArg___lam__4(
        v_____do__lift_5623_,
        v_____do__lift_5624_,
        v_id_5625_,
        v_toPure_5626_,
        v_enableLog_boxed_5638_,
        v___f_5628_,
        v_inst_5629_,
        v_inst_5630_,
        v_inst_5631_,
        v_inst_5632_,
        v_inst_5633_,
        v_toBind_5634_,
        v_getEnv_5635_,
        v_getOpenDecls_5636_,
        v_____do__lift_5637_,
    );
    return v_res_5639_;
}
pub unsafe fn l_Lean_resolveGlobalName___redArg___lam__5(
    mut v_inst_5640_: *mut leanh::LeanObject,
    mut v_____do__lift_5641_: *mut leanh::LeanObject,
    mut v_id_5642_: *mut leanh::LeanObject,
    mut v_toPure_5643_: *mut leanh::LeanObject,
    mut v_enableLog_5644_: u8,
    mut v___f_5645_: *mut leanh::LeanObject,
    mut v_inst_5646_: *mut leanh::LeanObject,
    mut v_inst_5647_: *mut leanh::LeanObject,
    mut v_inst_5648_: *mut leanh::LeanObject,
    mut v_inst_5649_: *mut leanh::LeanObject,
    mut v_inst_5650_: *mut leanh::LeanObject,
    mut v_toBind_5651_: *mut leanh::LeanObject,
    mut v_getEnv_5652_: *mut leanh::LeanObject,
    mut v_____do__lift_5653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getCurrNamespace_5654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getOpenDecls_5655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getCurrNamespace_5654_ = leanh::lean_ctor_get(v_inst_5640_, 0);
    leanh::lean_inc(v_getCurrNamespace_5654_);
    v_getOpenDecls_5655_ = leanh::lean_ctor_get(v_inst_5640_, 1);
    leanh::lean_inc(v_getOpenDecls_5655_);
    leanh::lean_dec_ref(v_inst_5640_);
    v___x_5656_ = leanh::lean_box((v_enableLog_5644_) as usize);
    leanh::lean_inc(v_toBind_5651_);
    v___f_5657_ = leanh::lean_alloc_closure(
        l_Lean_resolveGlobalName___redArg___lam__4___boxed as *mut core::ffi::c_void,
        15,
        14,
    );
    leanh::lean_closure_set(v___f_5657_, 0, v_____do__lift_5641_);
    leanh::lean_closure_set(v___f_5657_, 1, v_____do__lift_5653_);
    leanh::lean_closure_set(v___f_5657_, 2, v_id_5642_);
    leanh::lean_closure_set(v___f_5657_, 3, v_toPure_5643_);
    leanh::lean_closure_set(v___f_5657_, 4, v___x_5656_);
    leanh::lean_closure_set(v___f_5657_, 5, v___f_5645_);
    leanh::lean_closure_set(v___f_5657_, 6, v_inst_5646_);
    leanh::lean_closure_set(v___f_5657_, 7, v_inst_5647_);
    leanh::lean_closure_set(v___f_5657_, 8, v_inst_5648_);
    leanh::lean_closure_set(v___f_5657_, 9, v_inst_5649_);
    leanh::lean_closure_set(v___f_5657_, 10, v_inst_5650_);
    leanh::lean_closure_set(v___f_5657_, 11, v_toBind_5651_);
    leanh::lean_closure_set(v___f_5657_, 12, v_getEnv_5652_);
    leanh::lean_closure_set(v___f_5657_, 13, v_getOpenDecls_5655_);
    v___x_5658_ = leanh::lean_apply_4(
        v_toBind_5651_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getCurrNamespace_5654_,
        v___f_5657_,
    );
    return v___x_5658_;
}
pub unsafe fn l_Lean_resolveGlobalName___redArg___lam__5___boxed(
    mut v_inst_5659_: *mut leanh::LeanObject,
    mut v_____do__lift_5660_: *mut leanh::LeanObject,
    mut v_id_5661_: *mut leanh::LeanObject,
    mut v_toPure_5662_: *mut leanh::LeanObject,
    mut v_enableLog_5663_: *mut leanh::LeanObject,
    mut v___f_5664_: *mut leanh::LeanObject,
    mut v_inst_5665_: *mut leanh::LeanObject,
    mut v_inst_5666_: *mut leanh::LeanObject,
    mut v_inst_5667_: *mut leanh::LeanObject,
    mut v_inst_5668_: *mut leanh::LeanObject,
    mut v_inst_5669_: *mut leanh::LeanObject,
    mut v_toBind_5670_: *mut leanh::LeanObject,
    mut v_getEnv_5671_: *mut leanh::LeanObject,
    mut v_____do__lift_5672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_enableLog_boxed_5673_: u8 = 0;
    let mut v_res_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_enableLog_boxed_5673_ = (leanh::lean_unbox(v_enableLog_5663_) as u8);
    v_res_5674_ = l_Lean_resolveGlobalName___redArg___lam__5(
        v_inst_5659_,
        v_____do__lift_5660_,
        v_id_5661_,
        v_toPure_5662_,
        v_enableLog_boxed_5673_,
        v___f_5664_,
        v_inst_5665_,
        v_inst_5666_,
        v_inst_5667_,
        v_inst_5668_,
        v_inst_5669_,
        v_toBind_5670_,
        v_getEnv_5671_,
        v_____do__lift_5672_,
    );
    return v_res_5674_;
}
pub unsafe fn l_Lean_resolveGlobalName___redArg___lam__6(
    mut v_inst_5675_: *mut leanh::LeanObject,
    mut v_id_5676_: *mut leanh::LeanObject,
    mut v_toPure_5677_: *mut leanh::LeanObject,
    mut v_enableLog_5678_: u8,
    mut v___f_5679_: *mut leanh::LeanObject,
    mut v_inst_5680_: *mut leanh::LeanObject,
    mut v_inst_5681_: *mut leanh::LeanObject,
    mut v_inst_5682_: *mut leanh::LeanObject,
    mut v_inst_5683_: *mut leanh::LeanObject,
    mut v_inst_5684_: *mut leanh::LeanObject,
    mut v_toBind_5685_: *mut leanh::LeanObject,
    mut v_getEnv_5686_: *mut leanh::LeanObject,
    mut v_____do__lift_5687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5688_ = leanh::lean_box((v_enableLog_5678_) as usize);
    leanh::lean_inc(v_toBind_5685_);
    leanh::lean_inc(v_inst_5682_);
    v___f_5689_ = leanh::lean_alloc_closure(
        l_Lean_resolveGlobalName___redArg___lam__5___boxed as *mut core::ffi::c_void,
        14,
        13,
    );
    leanh::lean_closure_set(v___f_5689_, 0, v_inst_5675_);
    leanh::lean_closure_set(v___f_5689_, 1, v_____do__lift_5687_);
    leanh::lean_closure_set(v___f_5689_, 2, v_id_5676_);
    leanh::lean_closure_set(v___f_5689_, 3, v_toPure_5677_);
    leanh::lean_closure_set(v___f_5689_, 4, v___x_5688_);
    leanh::lean_closure_set(v___f_5689_, 5, v___f_5679_);
    leanh::lean_closure_set(v___f_5689_, 6, v_inst_5680_);
    leanh::lean_closure_set(v___f_5689_, 7, v_inst_5681_);
    leanh::lean_closure_set(v___f_5689_, 8, v_inst_5682_);
    leanh::lean_closure_set(v___f_5689_, 9, v_inst_5683_);
    leanh::lean_closure_set(v___f_5689_, 10, v_inst_5684_);
    leanh::lean_closure_set(v___f_5689_, 11, v_toBind_5685_);
    leanh::lean_closure_set(v___f_5689_, 12, v_getEnv_5686_);
    v___x_5690_ = leanh::lean_apply_4(
        v_toBind_5685_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_5682_,
        v___f_5689_,
    );
    return v___x_5690_;
}
pub unsafe fn l_Lean_resolveGlobalName___redArg___lam__6___boxed(
    mut v_inst_5691_: *mut leanh::LeanObject,
    mut v_id_5692_: *mut leanh::LeanObject,
    mut v_toPure_5693_: *mut leanh::LeanObject,
    mut v_enableLog_5694_: *mut leanh::LeanObject,
    mut v___f_5695_: *mut leanh::LeanObject,
    mut v_inst_5696_: *mut leanh::LeanObject,
    mut v_inst_5697_: *mut leanh::LeanObject,
    mut v_inst_5698_: *mut leanh::LeanObject,
    mut v_inst_5699_: *mut leanh::LeanObject,
    mut v_inst_5700_: *mut leanh::LeanObject,
    mut v_toBind_5701_: *mut leanh::LeanObject,
    mut v_getEnv_5702_: *mut leanh::LeanObject,
    mut v_____do__lift_5703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_enableLog_boxed_5704_: u8 = 0;
    let mut v_res_5705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_enableLog_boxed_5704_ = (leanh::lean_unbox(v_enableLog_5694_) as u8);
    v_res_5705_ = l_Lean_resolveGlobalName___redArg___lam__6(
        v_inst_5691_,
        v_id_5692_,
        v_toPure_5693_,
        v_enableLog_boxed_5704_,
        v___f_5695_,
        v_inst_5696_,
        v_inst_5697_,
        v_inst_5698_,
        v_inst_5699_,
        v_inst_5700_,
        v_toBind_5701_,
        v_getEnv_5702_,
        v_____do__lift_5703_,
    );
    return v_res_5705_;
}
pub unsafe fn l_Lean_resolveGlobalName___redArg(
    mut v_inst_5707_: *mut leanh::LeanObject,
    mut v_inst_5708_: *mut leanh::LeanObject,
    mut v_inst_5709_: *mut leanh::LeanObject,
    mut v_inst_5710_: *mut leanh::LeanObject,
    mut v_inst_5711_: *mut leanh::LeanObject,
    mut v_inst_5712_: *mut leanh::LeanObject,
    mut v_id_5713_: *mut leanh::LeanObject,
    mut v_enableLog_5714_: u8,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_5717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5715_ = leanh::lean_ctor_get(v_inst_5707_, 0);
    v_toBind_5716_ = leanh::lean_ctor_get(v_inst_5707_, 1);
    leanh::lean_inc_n(v_toBind_5716_, 2);
    v_getEnv_5717_ = leanh::lean_ctor_get(v_inst_5709_, 0);
    leanh::lean_inc_n(v_getEnv_5717_, 2);
    v_toPure_5718_ = leanh::lean_ctor_get(v_toApplicative_5715_, 1);
    leanh::lean_inc(v_toPure_5718_);
    v___f_5719_ = l_Lean_resolveGlobalName___redArg___closed__0;
    v___x_5720_ = leanh::lean_box((v_enableLog_5714_) as usize);
    v___f_5721_ = leanh::lean_alloc_closure(
        l_Lean_resolveGlobalName___redArg___lam__6___boxed as *mut core::ffi::c_void,
        13,
        12,
    );
    leanh::lean_closure_set(v___f_5721_, 0, v_inst_5708_);
    leanh::lean_closure_set(v___f_5721_, 1, v_id_5713_);
    leanh::lean_closure_set(v___f_5721_, 2, v_toPure_5718_);
    leanh::lean_closure_set(v___f_5721_, 3, v___x_5720_);
    leanh::lean_closure_set(v___f_5721_, 4, v___f_5719_);
    leanh::lean_closure_set(v___f_5721_, 5, v_inst_5707_);
    leanh::lean_closure_set(v___f_5721_, 6, v_inst_5709_);
    leanh::lean_closure_set(v___f_5721_, 7, v_inst_5710_);
    leanh::lean_closure_set(v___f_5721_, 8, v_inst_5711_);
    leanh::lean_closure_set(v___f_5721_, 9, v_inst_5712_);
    leanh::lean_closure_set(v___f_5721_, 10, v_toBind_5716_);
    leanh::lean_closure_set(v___f_5721_, 11, v_getEnv_5717_);
    v___x_5722_ = leanh::lean_apply_4(
        v_toBind_5716_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_5717_,
        v___f_5721_,
    );
    return v___x_5722_;
}
pub unsafe fn l_Lean_resolveGlobalName___redArg___boxed(
    mut v_inst_5723_: *mut leanh::LeanObject,
    mut v_inst_5724_: *mut leanh::LeanObject,
    mut v_inst_5725_: *mut leanh::LeanObject,
    mut v_inst_5726_: *mut leanh::LeanObject,
    mut v_inst_5727_: *mut leanh::LeanObject,
    mut v_inst_5728_: *mut leanh::LeanObject,
    mut v_id_5729_: *mut leanh::LeanObject,
    mut v_enableLog_5730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_enableLog_boxed_5731_: u8 = 0;
    let mut v_res_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_enableLog_boxed_5731_ = (leanh::lean_unbox(v_enableLog_5730_) as u8);
    v_res_5732_ = l_Lean_resolveGlobalName___redArg(
        v_inst_5723_,
        v_inst_5724_,
        v_inst_5725_,
        v_inst_5726_,
        v_inst_5727_,
        v_inst_5728_,
        v_id_5729_,
        v_enableLog_boxed_5731_,
    );
    return v_res_5732_;
}
pub unsafe fn l_Lean_resolveGlobalName(
    mut v_m_5733_: *mut leanh::LeanObject,
    mut v_inst_5734_: *mut leanh::LeanObject,
    mut v_inst_5735_: *mut leanh::LeanObject,
    mut v_inst_5736_: *mut leanh::LeanObject,
    mut v_inst_5737_: *mut leanh::LeanObject,
    mut v_inst_5738_: *mut leanh::LeanObject,
    mut v_inst_5739_: *mut leanh::LeanObject,
    mut v_id_5740_: *mut leanh::LeanObject,
    mut v_enableLog_5741_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_5742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5742_ = l_Lean_resolveGlobalName___redArg(
        v_inst_5734_,
        v_inst_5735_,
        v_inst_5736_,
        v_inst_5737_,
        v_inst_5738_,
        v_inst_5739_,
        v_id_5740_,
        v_enableLog_5741_,
    );
    return v___x_5742_;
}
pub unsafe fn l_Lean_resolveGlobalName___boxed(
    mut v_m_5743_: *mut leanh::LeanObject,
    mut v_inst_5744_: *mut leanh::LeanObject,
    mut v_inst_5745_: *mut leanh::LeanObject,
    mut v_inst_5746_: *mut leanh::LeanObject,
    mut v_inst_5747_: *mut leanh::LeanObject,
    mut v_inst_5748_: *mut leanh::LeanObject,
    mut v_inst_5749_: *mut leanh::LeanObject,
    mut v_id_5750_: *mut leanh::LeanObject,
    mut v_enableLog_5751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_enableLog_boxed_5752_: u8 = 0;
    let mut v_res_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_enableLog_boxed_5752_ = (leanh::lean_unbox(v_enableLog_5751_) as u8);
    v_res_5753_ = l_Lean_resolveGlobalName(
        v_m_5743_,
        v_inst_5744_,
        v_inst_5745_,
        v_inst_5746_,
        v_inst_5747_,
        v_inst_5748_,
        v_inst_5749_,
        v_id_5750_,
        v_enableLog_boxed_5752_,
    );
    return v_res_5753_;
}
pub unsafe fn l_Lean_resolveNamespaceCore___redArg___lam__0(
    mut v_toPure_5754_: *mut leanh::LeanObject,
    mut v_nss_5755_: *mut leanh::LeanObject,
    mut v_____r_5756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5757_ =
        leanh::lean_apply_2(v_toPure_5754_, leanh::lean_box(0), v_nss_5755_);
    return v___x_5757_;
}
pub unsafe fn l_Lean_resolveNamespaceCore___redArg___lam__1(
    mut v_____do__lift_5760_: *mut leanh::LeanObject,
    mut v_____do__lift_5761_: *mut leanh::LeanObject,
    mut v_id_5762_: *mut leanh::LeanObject,
    mut v_allowEmpty_5763_: u8,
    mut v_toPure_5764_: *mut leanh::LeanObject,
    mut v_inst_5765_: *mut leanh::LeanObject,
    mut v_inst_5766_: *mut leanh::LeanObject,
    mut v_toBind_5767_: *mut leanh::LeanObject,
    mut v_____do__lift_5768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nss_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_id_5762_);
    v_nss_5769_ = l_Lean_ResolveName_resolveNamespace(
        v_____do__lift_5760_,
        v_____do__lift_5761_,
        v_____do__lift_5768_,
        v_id_5762_,
    );
    if v_allowEmpty_5763_ == 0 {
        let mut v___x_5770_: u8 = 0;
        v___x_5770_ = l_List_isEmpty___redArg(v_nss_5769_);
        if v___x_5770_ == 0 {
            let mut v___x_5771_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_5767_);
            leanh::lean_dec_ref(v_inst_5766_);
            leanh::lean_dec_ref(v_inst_5765_);
            leanh::lean_dec(v_id_5762_);
            v___x_5771_ =
                leanh::lean_apply_2(v_toPure_5764_, leanh::lean_box(0), v_nss_5769_);
            return v___x_5771_;
        } else {
            let mut v___f_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5773_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___f_5772_ = leanh::lean_alloc_closure(
                l_Lean_resolveNamespaceCore___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                2,
            );
            leanh::lean_closure_set(v___f_5772_, 0, v_toPure_5764_);
            leanh::lean_closure_set(v___f_5772_, 1, v_nss_5769_);
            v___x_5773_ = l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0;
            v___x_5774_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                v_id_5762_,
                v___x_5770_,
            );
            v___x_5775_ = lean_string_append(v___x_5773_, v___x_5774_);
            leanh::lean_dec_ref(v___x_5774_);
            v___x_5776_ = l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1;
            v___x_5777_ = lean_string_append(v___x_5775_, v___x_5776_);
            v___x_5778_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_5778_, 0, v___x_5777_);
            v___x_5779_ = l_Lean_MessageData_ofFormat(v___x_5778_);
            v___x_5780_ = l_Lean_throwError___redArg(v_inst_5765_, v_inst_5766_, v___x_5779_);
            v___x_5781_ = leanh::lean_apply_4(
                v_toBind_5767_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_5780_,
                v___f_5772_,
            );
            return v___x_5781_;
        }
    } else {
        let mut v___x_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toBind_5767_);
        leanh::lean_dec_ref(v_inst_5766_);
        leanh::lean_dec_ref(v_inst_5765_);
        leanh::lean_dec(v_id_5762_);
        v___x_5782_ =
            leanh::lean_apply_2(v_toPure_5764_, leanh::lean_box(0), v_nss_5769_);
        return v___x_5782_;
    }
}
pub unsafe fn l_Lean_resolveNamespaceCore___redArg___lam__1___boxed(
    mut v_____do__lift_5783_: *mut leanh::LeanObject,
    mut v_____do__lift_5784_: *mut leanh::LeanObject,
    mut v_id_5785_: *mut leanh::LeanObject,
    mut v_allowEmpty_5786_: *mut leanh::LeanObject,
    mut v_toPure_5787_: *mut leanh::LeanObject,
    mut v_inst_5788_: *mut leanh::LeanObject,
    mut v_inst_5789_: *mut leanh::LeanObject,
    mut v_toBind_5790_: *mut leanh::LeanObject,
    mut v_____do__lift_5791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowEmpty_boxed_5792_: u8 = 0;
    let mut v_res_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowEmpty_boxed_5792_ = (leanh::lean_unbox(v_allowEmpty_5786_) as u8);
    v_res_5793_ = l_Lean_resolveNamespaceCore___redArg___lam__1(
        v_____do__lift_5783_,
        v_____do__lift_5784_,
        v_id_5785_,
        v_allowEmpty_boxed_5792_,
        v_toPure_5787_,
        v_inst_5788_,
        v_inst_5789_,
        v_toBind_5790_,
        v_____do__lift_5791_,
    );
    return v_res_5793_;
}
pub unsafe fn l_Lean_resolveNamespaceCore___redArg___lam__2(
    mut v_____do__lift_5794_: *mut leanh::LeanObject,
    mut v_id_5795_: *mut leanh::LeanObject,
    mut v_allowEmpty_5796_: u8,
    mut v_toPure_5797_: *mut leanh::LeanObject,
    mut v_inst_5798_: *mut leanh::LeanObject,
    mut v_inst_5799_: *mut leanh::LeanObject,
    mut v_toBind_5800_: *mut leanh::LeanObject,
    mut v_getOpenDecls_5801_: *mut leanh::LeanObject,
    mut v_____do__lift_5802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5803_ = leanh::lean_box((v_allowEmpty_5796_) as usize);
    leanh::lean_inc(v_toBind_5800_);
    v___f_5804_ = leanh::lean_alloc_closure(
        l_Lean_resolveNamespaceCore___redArg___lam__1___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_5804_, 0, v_____do__lift_5794_);
    leanh::lean_closure_set(v___f_5804_, 1, v_____do__lift_5802_);
    leanh::lean_closure_set(v___f_5804_, 2, v_id_5795_);
    leanh::lean_closure_set(v___f_5804_, 3, v___x_5803_);
    leanh::lean_closure_set(v___f_5804_, 4, v_toPure_5797_);
    leanh::lean_closure_set(v___f_5804_, 5, v_inst_5798_);
    leanh::lean_closure_set(v___f_5804_, 6, v_inst_5799_);
    leanh::lean_closure_set(v___f_5804_, 7, v_toBind_5800_);
    v___x_5805_ = leanh::lean_apply_4(
        v_toBind_5800_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getOpenDecls_5801_,
        v___f_5804_,
    );
    return v___x_5805_;
}
pub unsafe fn l_Lean_resolveNamespaceCore___redArg___lam__2___boxed(
    mut v_____do__lift_5806_: *mut leanh::LeanObject,
    mut v_id_5807_: *mut leanh::LeanObject,
    mut v_allowEmpty_5808_: *mut leanh::LeanObject,
    mut v_toPure_5809_: *mut leanh::LeanObject,
    mut v_inst_5810_: *mut leanh::LeanObject,
    mut v_inst_5811_: *mut leanh::LeanObject,
    mut v_toBind_5812_: *mut leanh::LeanObject,
    mut v_getOpenDecls_5813_: *mut leanh::LeanObject,
    mut v_____do__lift_5814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowEmpty_boxed_5815_: u8 = 0;
    let mut v_res_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowEmpty_boxed_5815_ = (leanh::lean_unbox(v_allowEmpty_5808_) as u8);
    v_res_5816_ = l_Lean_resolveNamespaceCore___redArg___lam__2(
        v_____do__lift_5806_,
        v_id_5807_,
        v_allowEmpty_boxed_5815_,
        v_toPure_5809_,
        v_inst_5810_,
        v_inst_5811_,
        v_toBind_5812_,
        v_getOpenDecls_5813_,
        v_____do__lift_5814_,
    );
    return v_res_5816_;
}
pub unsafe fn l_Lean_resolveNamespaceCore___redArg___lam__3(
    mut v_inst_5817_: *mut leanh::LeanObject,
    mut v_id_5818_: *mut leanh::LeanObject,
    mut v_allowEmpty_5819_: u8,
    mut v_toPure_5820_: *mut leanh::LeanObject,
    mut v_inst_5821_: *mut leanh::LeanObject,
    mut v_inst_5822_: *mut leanh::LeanObject,
    mut v_toBind_5823_: *mut leanh::LeanObject,
    mut v_____do__lift_5824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getCurrNamespace_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getOpenDecls_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getCurrNamespace_5825_ = leanh::lean_ctor_get(v_inst_5817_, 0);
    leanh::lean_inc(v_getCurrNamespace_5825_);
    v_getOpenDecls_5826_ = leanh::lean_ctor_get(v_inst_5817_, 1);
    leanh::lean_inc(v_getOpenDecls_5826_);
    leanh::lean_dec_ref(v_inst_5817_);
    v___x_5827_ = leanh::lean_box((v_allowEmpty_5819_) as usize);
    leanh::lean_inc(v_toBind_5823_);
    v___f_5828_ = leanh::lean_alloc_closure(
        l_Lean_resolveNamespaceCore___redArg___lam__2___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_5828_, 0, v_____do__lift_5824_);
    leanh::lean_closure_set(v___f_5828_, 1, v_id_5818_);
    leanh::lean_closure_set(v___f_5828_, 2, v___x_5827_);
    leanh::lean_closure_set(v___f_5828_, 3, v_toPure_5820_);
    leanh::lean_closure_set(v___f_5828_, 4, v_inst_5821_);
    leanh::lean_closure_set(v___f_5828_, 5, v_inst_5822_);
    leanh::lean_closure_set(v___f_5828_, 6, v_toBind_5823_);
    leanh::lean_closure_set(v___f_5828_, 7, v_getOpenDecls_5826_);
    v___x_5829_ = leanh::lean_apply_4(
        v_toBind_5823_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getCurrNamespace_5825_,
        v___f_5828_,
    );
    return v___x_5829_;
}
pub unsafe fn l_Lean_resolveNamespaceCore___redArg___lam__3___boxed(
    mut v_inst_5830_: *mut leanh::LeanObject,
    mut v_id_5831_: *mut leanh::LeanObject,
    mut v_allowEmpty_5832_: *mut leanh::LeanObject,
    mut v_toPure_5833_: *mut leanh::LeanObject,
    mut v_inst_5834_: *mut leanh::LeanObject,
    mut v_inst_5835_: *mut leanh::LeanObject,
    mut v_toBind_5836_: *mut leanh::LeanObject,
    mut v_____do__lift_5837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowEmpty_boxed_5838_: u8 = 0;
    let mut v_res_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowEmpty_boxed_5838_ = (leanh::lean_unbox(v_allowEmpty_5832_) as u8);
    v_res_5839_ = l_Lean_resolveNamespaceCore___redArg___lam__3(
        v_inst_5830_,
        v_id_5831_,
        v_allowEmpty_boxed_5838_,
        v_toPure_5833_,
        v_inst_5834_,
        v_inst_5835_,
        v_toBind_5836_,
        v_____do__lift_5837_,
    );
    return v_res_5839_;
}
pub unsafe fn l_Lean_resolveNamespaceCore___redArg(
    mut v_inst_5840_: *mut leanh::LeanObject,
    mut v_inst_5841_: *mut leanh::LeanObject,
    mut v_inst_5842_: *mut leanh::LeanObject,
    mut v_inst_5843_: *mut leanh::LeanObject,
    mut v_id_5844_: *mut leanh::LeanObject,
    mut v_allowEmpty_5845_: u8,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_5846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_5848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5846_ = leanh::lean_ctor_get(v_inst_5840_, 0);
    v_toBind_5847_ = leanh::lean_ctor_get(v_inst_5840_, 1);
    leanh::lean_inc_n(v_toBind_5847_, 2);
    v_getEnv_5848_ = leanh::lean_ctor_get(v_inst_5842_, 0);
    leanh::lean_inc(v_getEnv_5848_);
    leanh::lean_dec_ref(v_inst_5842_);
    v_toPure_5849_ = leanh::lean_ctor_get(v_toApplicative_5846_, 1);
    leanh::lean_inc(v_toPure_5849_);
    v___x_5850_ = leanh::lean_box((v_allowEmpty_5845_) as usize);
    v___f_5851_ = leanh::lean_alloc_closure(
        l_Lean_resolveNamespaceCore___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_5851_, 0, v_inst_5841_);
    leanh::lean_closure_set(v___f_5851_, 1, v_id_5844_);
    leanh::lean_closure_set(v___f_5851_, 2, v___x_5850_);
    leanh::lean_closure_set(v___f_5851_, 3, v_toPure_5849_);
    leanh::lean_closure_set(v___f_5851_, 4, v_inst_5840_);
    leanh::lean_closure_set(v___f_5851_, 5, v_inst_5843_);
    leanh::lean_closure_set(v___f_5851_, 6, v_toBind_5847_);
    v___x_5852_ = leanh::lean_apply_4(
        v_toBind_5847_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_5848_,
        v___f_5851_,
    );
    return v___x_5852_;
}
pub unsafe fn l_Lean_resolveNamespaceCore___redArg___boxed(
    mut v_inst_5853_: *mut leanh::LeanObject,
    mut v_inst_5854_: *mut leanh::LeanObject,
    mut v_inst_5855_: *mut leanh::LeanObject,
    mut v_inst_5856_: *mut leanh::LeanObject,
    mut v_id_5857_: *mut leanh::LeanObject,
    mut v_allowEmpty_5858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowEmpty_boxed_5859_: u8 = 0;
    let mut v_res_5860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowEmpty_boxed_5859_ = (leanh::lean_unbox(v_allowEmpty_5858_) as u8);
    v_res_5860_ = l_Lean_resolveNamespaceCore___redArg(
        v_inst_5853_,
        v_inst_5854_,
        v_inst_5855_,
        v_inst_5856_,
        v_id_5857_,
        v_allowEmpty_boxed_5859_,
    );
    return v_res_5860_;
}
pub unsafe fn l_Lean_resolveNamespaceCore(
    mut v_m_5861_: *mut leanh::LeanObject,
    mut v_inst_5862_: *mut leanh::LeanObject,
    mut v_inst_5863_: *mut leanh::LeanObject,
    mut v_inst_5864_: *mut leanh::LeanObject,
    mut v_inst_5865_: *mut leanh::LeanObject,
    mut v_id_5866_: *mut leanh::LeanObject,
    mut v_allowEmpty_5867_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_5868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5868_ = l_Lean_resolveNamespaceCore___redArg(
        v_inst_5862_,
        v_inst_5863_,
        v_inst_5864_,
        v_inst_5865_,
        v_id_5866_,
        v_allowEmpty_5867_,
    );
    return v___x_5868_;
}
pub unsafe fn l_Lean_resolveNamespaceCore___boxed(
    mut v_m_5869_: *mut leanh::LeanObject,
    mut v_inst_5870_: *mut leanh::LeanObject,
    mut v_inst_5871_: *mut leanh::LeanObject,
    mut v_inst_5872_: *mut leanh::LeanObject,
    mut v_inst_5873_: *mut leanh::LeanObject,
    mut v_id_5874_: *mut leanh::LeanObject,
    mut v_allowEmpty_5875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowEmpty_boxed_5876_: u8 = 0;
    let mut v_res_5877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowEmpty_boxed_5876_ = (leanh::lean_unbox(v_allowEmpty_5875_) as u8);
    v_res_5877_ = l_Lean_resolveNamespaceCore(
        v_m_5869_,
        v_inst_5870_,
        v_inst_5871_,
        v_inst_5872_,
        v_inst_5873_,
        v_id_5874_,
        v_allowEmpty_boxed_5876_,
    );
    return v_res_5877_;
}
pub unsafe fn l_Lean_resolveNamespace___redArg___lam__0(
    mut v_x_5878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ns_5879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5882_: u8 = 0;
    let mut v___x_5884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5886_: u8 = 0;
    let mut v___x_5887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5878_) == 0 {
                    v_ns_5879_ = leanh::lean_ctor_get(v_x_5878_, 0);
                    v_isSharedCheck_5886_ = (!leanh::lean_is_exclusive(v_x_5878_)) as u8;
                    if v_isSharedCheck_5886_ == 0 {
                        v___x_5881_ = v_x_5878_;
                        v_isShared_5882_ = v_isSharedCheck_5886_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_ns_5879_);
                        leanh::lean_dec(v_x_5878_);
                        v___x_5881_ = leanh::lean_box(0);
                        v_isShared_5882_ = v_isSharedCheck_5886_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_5878_);
                    v___x_5887_ = leanh::lean_box(0);
                    return v___x_5887_;
                }
            }
            1 => {
                if v_isShared_5882_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5881_, 1);
                    v___x_5884_ = v___x_5881_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5885_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5885_, 0, v_ns_5879_);
                    v___x_5884_ = v_reuseFailAlloc_5885_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5884_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_resolveNamespace___redArg___lam__1(
    mut v_x_5888_: *mut leanh::LeanObject,
    mut v_withRef_5889_: *mut leanh::LeanObject,
    mut v___x_5890_: *mut leanh::LeanObject,
    mut v_oldRef_5891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_5892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_5892_ = l_Lean_replaceRef(v_x_5888_, v_oldRef_5891_);
    v___x_5893_ = leanh::lean_apply_3(
        v_withRef_5889_,
        leanh::lean_box(0),
        v_ref_5892_,
        v___x_5890_,
    );
    return v___x_5893_;
}
pub unsafe fn l_Lean_resolveNamespace___redArg___lam__1___boxed(
    mut v_x_5894_: *mut leanh::LeanObject,
    mut v_withRef_5895_: *mut leanh::LeanObject,
    mut v___x_5896_: *mut leanh::LeanObject,
    mut v_oldRef_5897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5898_ = l_Lean_resolveNamespace___redArg___lam__1(
        v_x_5894_,
        v_withRef_5895_,
        v___x_5896_,
        v_oldRef_5897_,
    );
    leanh::lean_dec(v_oldRef_5897_);
    leanh::lean_dec(v_x_5894_);
    return v_res_5898_;
}
pub unsafe fn _init_l_Lean_resolveNamespace___redArg___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5905_ = l_Lean_resolveNamespace___redArg___closed__3;
    v___x_5906_ = l_Lean_MessageData_ofFormat(v___x_5905_);
    return v___x_5906_;
}
pub unsafe fn l_Lean_resolveNamespace___redArg(
    mut v_inst_5907_: *mut leanh::LeanObject,
    mut v_inst_5908_: *mut leanh::LeanObject,
    mut v_inst_5909_: *mut leanh::LeanObject,
    mut v_inst_5910_: *mut leanh::LeanObject,
    mut v_x_5911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5911_) == 3 {
        let mut v_val_5912_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_preresolved_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5914_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_pre_5916_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5917_: u8 = 0;
        v_val_5912_ = leanh::lean_ctor_get(v_x_5911_, 2);
        v_preresolved_5913_ = leanh::lean_ctor_get(v_x_5911_, 3);
        v___f_5914_ = l_Lean_resolveNamespace___redArg___closed__0;
        v___x_5915_ = l_Lean_resolveNamespace___redArg___closed__1;
        leanh::lean_inc(v_preresolved_5913_);
        v_pre_5916_ = l_List_filterMapTR_go___redArg(v___f_5914_, v_preresolved_5913_, v___x_5915_);
        v___x_5917_ = l_List_isEmpty___redArg(v_pre_5916_);
        if v___x_5917_ == 0 {
            let mut v_toApplicative_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5919_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v_x_5911_, 4);
            leanh::lean_dec_ref(v_inst_5910_);
            leanh::lean_dec_ref(v_inst_5909_);
            leanh::lean_dec_ref(v_inst_5908_);
            v_toApplicative_5918_ = leanh::lean_ctor_get(v_inst_5907_, 0);
            leanh::lean_inc_ref(v_toApplicative_5918_);
            leanh::lean_dec_ref(v_inst_5907_);
            v_toPure_5919_ = leanh::lean_ctor_get(v_toApplicative_5918_, 1);
            leanh::lean_inc(v_toPure_5919_);
            leanh::lean_dec_ref(v_toApplicative_5918_);
            v___x_5920_ =
                leanh::lean_apply_2(v_toPure_5919_, leanh::lean_box(0), v_pre_5916_);
            return v___x_5920_;
        } else {
            let mut v_toMonadRef_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_getRef_5923_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_withRef_5924_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5925_: u8 = 0;
            let mut v___x_5926_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_pre_5916_);
            v_toMonadRef_5921_ = leanh::lean_ctor_get(v_inst_5910_, 1);
            v_toBind_5922_ = leanh::lean_ctor_get(v_inst_5907_, 1);
            leanh::lean_inc(v_toBind_5922_);
            v_getRef_5923_ = leanh::lean_ctor_get(v_toMonadRef_5921_, 0);
            leanh::lean_inc(v_getRef_5923_);
            v_withRef_5924_ = leanh::lean_ctor_get(v_toMonadRef_5921_, 1);
            leanh::lean_inc(v_withRef_5924_);
            v___x_5925_ = 0;
            leanh::lean_inc(v_val_5912_);
            v___x_5926_ = l_Lean_resolveNamespaceCore___redArg(
                v_inst_5907_,
                v_inst_5908_,
                v_inst_5909_,
                v_inst_5910_,
                v_val_5912_,
                v___x_5925_,
            );
            v___f_5927_ = leanh::lean_alloc_closure(
                l_Lean_resolveNamespace___redArg___lam__1___boxed as *mut core::ffi::c_void,
                4,
                3,
            );
            leanh::lean_closure_set(v___f_5927_, 0, v_x_5911_);
            leanh::lean_closure_set(v___f_5927_, 1, v_withRef_5924_);
            leanh::lean_closure_set(v___f_5927_, 2, v___x_5926_);
            v___x_5928_ = leanh::lean_apply_4(
                v_toBind_5922_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_getRef_5923_,
                v___f_5927_,
            );
            return v___x_5928_;
        }
    } else {
        let mut v___x_5929_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5930_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_5909_);
        leanh::lean_dec_ref(v_inst_5908_);
        v___x_5929_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_resolveNamespace___redArg___closed__4),
            core::ptr::addr_of_mut!(l_Lean_resolveNamespace___redArg___closed__4_once),
            _init_l_Lean_resolveNamespace___redArg___closed__4,
        );
        v___x_5930_ =
            l_Lean_throwErrorAt___redArg(v_inst_5907_, v_inst_5910_, v_x_5911_, v___x_5929_);
        return v___x_5930_;
    }
}
pub unsafe fn l_Lean_resolveNamespace(
    mut v_m_5931_: *mut leanh::LeanObject,
    mut v_inst_5932_: *mut leanh::LeanObject,
    mut v_inst_5933_: *mut leanh::LeanObject,
    mut v_inst_5934_: *mut leanh::LeanObject,
    mut v_inst_5935_: *mut leanh::LeanObject,
    mut v_x_5936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5937_ = l_Lean_resolveNamespace___redArg(
        v_inst_5932_,
        v_inst_5933_,
        v_inst_5934_,
        v_inst_5935_,
        v_x_5936_,
    );
    return v___x_5937_;
}
pub unsafe fn l_Lean_resolveUniqueNamespace___redArg___lam__0(
    mut v_id_5940_: *mut leanh::LeanObject,
    mut v___f_5941_: *mut leanh::LeanObject,
    mut v_inst_5942_: *mut leanh::LeanObject,
    mut v_inst_5943_: *mut leanh::LeanObject,
    mut v_toPure_5944_: *mut leanh::LeanObject,
    mut v_____do__lift_5945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: u8 = 0;
    let mut v___x_5950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_5945_) == 1 {
                    v_tail_5961_ = leanh::lean_ctor_get(v_____do__lift_5945_, 1);
                    if leanh::lean_obj_tag(v_tail_5961_) == 0 {
                        leanh::lean_dec_ref(v_inst_5943_);
                        leanh::lean_dec_ref(v_inst_5942_);
                        leanh::lean_dec_ref(v___f_5941_);
                        v_head_5962_ = leanh::lean_ctor_get(v_____do__lift_5945_, 0);
                        leanh::lean_inc(v_head_5962_);
                        leanh::lean_dec_ref_known(v_____do__lift_5945_, 2);
                        v___x_5963_ = leanh::lean_apply_2(
                            v_toPure_5944_,
                            leanh::lean_box(0),
                            v_head_5962_,
                        );
                        return v___x_5963_;
                    } else {
                        leanh::lean_dec(v_toPure_5944_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_toPure_5944_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5947_ = l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0;
                v___x_5948_ = l_Lean_TSyntax_getId(v_id_5940_);
                v___x_5949_ = 1;
                v___x_5950_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v___x_5948_,
                    v___x_5949_,
                );
                v___x_5951_ = lean_string_append(v___x_5947_, v___x_5950_);
                leanh::lean_dec_ref(v___x_5950_);
                v___x_5952_ = l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1;
                v___x_5953_ = lean_string_append(v___x_5951_, v___x_5952_);
                v___x_5954_ = l_List_toString___redArg(v___f_5941_, v_____do__lift_5945_);
                v___x_5955_ = lean_string_append(v___x_5953_, v___x_5954_);
                leanh::lean_dec_ref(v___x_5954_);
                v___x_5956_ = l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1;
                v___x_5957_ = lean_string_append(v___x_5955_, v___x_5956_);
                v___x_5958_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5958_, 0, v___x_5957_);
                v___x_5959_ = l_Lean_MessageData_ofFormat(v___x_5958_);
                v___x_5960_ = l_Lean_throwError___redArg(v_inst_5942_, v_inst_5943_, v___x_5959_);
                return v___x_5960_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed(
    mut v_id_5964_: *mut leanh::LeanObject,
    mut v___f_5965_: *mut leanh::LeanObject,
    mut v_inst_5966_: *mut leanh::LeanObject,
    mut v_inst_5967_: *mut leanh::LeanObject,
    mut v_toPure_5968_: *mut leanh::LeanObject,
    mut v_____do__lift_5969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5970_ = l_Lean_resolveUniqueNamespace___redArg___lam__0(
        v_id_5964_,
        v___f_5965_,
        v_inst_5966_,
        v_inst_5967_,
        v_toPure_5968_,
        v_____do__lift_5969_,
    );
    leanh::lean_dec(v_id_5964_);
    return v_res_5970_;
}
pub unsafe fn l_Lean_resolveUniqueNamespace___redArg(
    mut v_inst_5972_: *mut leanh::LeanObject,
    mut v_inst_5973_: *mut leanh::LeanObject,
    mut v_inst_5974_: *mut leanh::LeanObject,
    mut v_inst_5975_: *mut leanh::LeanObject,
    mut v_id_5976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_5977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5977_ = leanh::lean_ctor_get(v_inst_5972_, 0);
    v_toBind_5978_ = leanh::lean_ctor_get(v_inst_5972_, 1);
    leanh::lean_inc(v_toBind_5978_);
    v_toPure_5979_ = leanh::lean_ctor_get(v_toApplicative_5977_, 1);
    leanh::lean_inc(v_toPure_5979_);
    v___f_5980_ = l_Lean_resolveUniqueNamespace___redArg___closed__0;
    leanh::lean_inc(v_id_5976_);
    leanh::lean_inc_ref(v_inst_5975_);
    leanh::lean_inc_ref(v_inst_5972_);
    v___x_5981_ = l_Lean_resolveNamespace___redArg(
        v_inst_5972_,
        v_inst_5973_,
        v_inst_5974_,
        v_inst_5975_,
        v_id_5976_,
    );
    v___f_5982_ = leanh::lean_alloc_closure(
        l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_5982_, 0, v_id_5976_);
    leanh::lean_closure_set(v___f_5982_, 1, v___f_5980_);
    leanh::lean_closure_set(v___f_5982_, 2, v_inst_5972_);
    leanh::lean_closure_set(v___f_5982_, 3, v_inst_5975_);
    leanh::lean_closure_set(v___f_5982_, 4, v_toPure_5979_);
    v___x_5983_ = leanh::lean_apply_4(
        v_toBind_5978_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5981_,
        v___f_5982_,
    );
    return v___x_5983_;
}
pub unsafe fn l_Lean_resolveUniqueNamespace(
    mut v_m_5984_: *mut leanh::LeanObject,
    mut v_inst_5985_: *mut leanh::LeanObject,
    mut v_inst_5986_: *mut leanh::LeanObject,
    mut v_inst_5987_: *mut leanh::LeanObject,
    mut v_inst_5988_: *mut leanh::LeanObject,
    mut v_id_5989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5990_ = l_Lean_resolveUniqueNamespace___redArg(
        v_inst_5985_,
        v_inst_5986_,
        v_inst_5987_,
        v_inst_5988_,
        v_id_5989_,
    );
    return v___x_5990_;
}
pub unsafe fn l_Lean_filterFieldList___redArg___lam__0(
    mut v_x_5991_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_snd_5992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: u8 = 0;
    v_snd_5992_ = leanh::lean_ctor_get(v_x_5991_, 1);
    v___x_5993_ = l_List_isEmpty___redArg(v_snd_5992_);
    return v___x_5993_;
}
pub unsafe fn l_Lean_filterFieldList___redArg___lam__0___boxed(
    mut v_x_5994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5995_: u8 = 0;
    let mut v_r_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5995_ = l_Lean_filterFieldList___redArg___lam__0(v_x_5994_);
    leanh::lean_dec_ref(v_x_5994_);
    v_r_5996_ = leanh::lean_box((v_res_5995_) as usize);
    return v_r_5996_;
}
pub unsafe fn l_Lean_filterFieldList___redArg___lam__1(
    mut v_x_5997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_5998_ = leanh::lean_ctor_get(v_x_5997_, 0);
    leanh::lean_inc(v_fst_5998_);
    return v_fst_5998_;
}
pub unsafe fn l_Lean_filterFieldList___redArg___lam__1___boxed(
    mut v_x_5999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6000_ = l_Lean_filterFieldList___redArg___lam__1(v_x_5999_);
    leanh::lean_dec_ref(v_x_5999_);
    return v_res_6000_;
}
pub unsafe fn l_Lean_filterFieldList___redArg___lam__2(
    mut v___f_6001_: *mut leanh::LeanObject,
    mut v_cs_6002_: *mut leanh::LeanObject,
    mut v_toPure_6003_: *mut leanh::LeanObject,
    mut v_____r_6004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6005_ = leanh::lean_box(0);
    v___x_6006_ = l_List_mapTR_loop___redArg(v___f_6001_, v_cs_6002_, v___x_6005_);
    v___x_6007_ =
        leanh::lean_apply_2(v_toPure_6003_, leanh::lean_box(0), v___x_6006_);
    return v___x_6007_;
}
pub unsafe fn l_Lean_filterFieldList___redArg___lam__3(
    mut v___f_6008_: *mut leanh::LeanObject,
    mut v_____r_6009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6010_ = leanh::lean_apply_1(v___f_6008_, v_____r_6009_);
    return v___x_6010_;
}
pub unsafe fn l_Lean_filterFieldList___redArg___lam__4(
    mut v_inst_6011_: *mut leanh::LeanObject,
    mut v_inst_6012_: *mut leanh::LeanObject,
    mut v_inst_6013_: *mut leanh::LeanObject,
    mut v_n_6014_: *mut leanh::LeanObject,
    mut v_toBind_6015_: *mut leanh::LeanObject,
    mut v___f_6016_: *mut leanh::LeanObject,
    mut v_____do__lift_6017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6018_ = l_Lean_throwUnknownConstantAt___redArg(
        v_inst_6011_,
        v_inst_6012_,
        v_inst_6013_,
        v_____do__lift_6017_,
        v_n_6014_,
    );
    v___x_6019_ = leanh::lean_apply_4(
        v_toBind_6015_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6018_,
        v___f_6016_,
    );
    return v___x_6019_;
}
pub unsafe fn l_Lean_filterFieldList___redArg(
    mut v_inst_6022_: *mut leanh::LeanObject,
    mut v_inst_6023_: *mut leanh::LeanObject,
    mut v_inst_6024_: *mut leanh::LeanObject,
    mut v_n_6025_: *mut leanh::LeanObject,
    mut v_cs_6026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_6027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cs_6033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: u8 = 0;
    v_toApplicative_6027_ = leanh::lean_ctor_get(v_inst_6022_, 0);
    v_toBind_6028_ = leanh::lean_ctor_get(v_inst_6022_, 1);
    leanh::lean_inc(v_toBind_6028_);
    v_toPure_6029_ = leanh::lean_ctor_get(v_toApplicative_6027_, 1);
    v___f_6030_ = l_Lean_filterFieldList___redArg___closed__0;
    v___f_6031_ = l_Lean_filterFieldList___redArg___closed__1;
    v___x_6032_ = leanh::lean_box(0);
    v_cs_6033_ = l_List_filterTR_loop___redArg(v___f_6030_, v_cs_6026_, v___x_6032_);
    leanh::lean_inc(v_toPure_6029_);
    leanh::lean_inc(v_cs_6033_);
    v___f_6034_ = leanh::lean_alloc_closure(
        l_Lean_filterFieldList___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_6034_, 0, v___f_6031_);
    leanh::lean_closure_set(v___f_6034_, 1, v_cs_6033_);
    leanh::lean_closure_set(v___f_6034_, 2, v_toPure_6029_);
    v___x_6035_ = l_List_isEmpty___redArg(v_cs_6033_);
    if v___x_6035_ == 0 {
        let mut v___x_6036_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6037_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_toPure_6029_);
        leanh::lean_dec_ref(v___f_6034_);
        leanh::lean_dec(v_toBind_6028_);
        leanh::lean_dec(v_n_6025_);
        leanh::lean_dec_ref(v_inst_6024_);
        leanh::lean_dec_ref(v_inst_6023_);
        leanh::lean_dec_ref(v_inst_6022_);
        v___x_6036_ = leanh::lean_box(0);
        v___x_6037_ = l_Lean_filterFieldList___redArg___lam__2(
            v___f_6031_,
            v_cs_6033_,
            v_toPure_6029_,
            v___x_6036_,
        );
        return v___x_6037_;
    } else {
        let mut v_toMonadRef_6038_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getRef_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6041_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6042_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_cs_6033_);
        v_toMonadRef_6038_ = leanh::lean_ctor_get(v_inst_6024_, 1);
        v_getRef_6039_ = leanh::lean_ctor_get(v_toMonadRef_6038_, 0);
        leanh::lean_inc(v_getRef_6039_);
        v___f_6040_ = leanh::lean_alloc_closure(
            l_Lean_filterFieldList___redArg___lam__3 as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_6040_, 0, v___f_6034_);
        leanh::lean_inc(v_toBind_6028_);
        v___f_6041_ = leanh::lean_alloc_closure(
            l_Lean_filterFieldList___redArg___lam__4 as *mut core::ffi::c_void,
            7,
            6,
        );
        leanh::lean_closure_set(v___f_6041_, 0, v_inst_6022_);
        leanh::lean_closure_set(v___f_6041_, 1, v_inst_6023_);
        leanh::lean_closure_set(v___f_6041_, 2, v_inst_6024_);
        leanh::lean_closure_set(v___f_6041_, 3, v_n_6025_);
        leanh::lean_closure_set(v___f_6041_, 4, v_toBind_6028_);
        leanh::lean_closure_set(v___f_6041_, 5, v___f_6040_);
        v___x_6042_ = leanh::lean_apply_4(
            v_toBind_6028_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getRef_6039_,
            v___f_6041_,
        );
        return v___x_6042_;
    }
}
pub unsafe fn l_Lean_filterFieldList(
    mut v_m_6043_: *mut leanh::LeanObject,
    mut v_inst_6044_: *mut leanh::LeanObject,
    mut v_inst_6045_: *mut leanh::LeanObject,
    mut v_inst_6046_: *mut leanh::LeanObject,
    mut v_n_6047_: *mut leanh::LeanObject,
    mut v_cs_6048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6049_ = l_Lean_filterFieldList___redArg(
        v_inst_6044_,
        v_inst_6045_,
        v_inst_6046_,
        v_n_6047_,
        v_cs_6048_,
    );
    return v___x_6049_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0(
    mut v_inst_6050_: *mut leanh::LeanObject,
    mut v_inst_6051_: *mut leanh::LeanObject,
    mut v_inst_6052_: *mut leanh::LeanObject,
    mut v_n_6053_: *mut leanh::LeanObject,
    mut v_cs_6054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6055_ = l_Lean_filterFieldList___redArg(
        v_inst_6050_,
        v_inst_6051_,
        v_inst_6052_,
        v_n_6053_,
        v_cs_6054_,
    );
    return v___x_6055_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(
    mut v_inst_6056_: *mut leanh::LeanObject,
    mut v_inst_6057_: *mut leanh::LeanObject,
    mut v_inst_6058_: *mut leanh::LeanObject,
    mut v_inst_6059_: *mut leanh::LeanObject,
    mut v_inst_6060_: *mut leanh::LeanObject,
    mut v_inst_6061_: *mut leanh::LeanObject,
    mut v_inst_6062_: *mut leanh::LeanObject,
    mut v_n_6063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_6064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: u8 = 0;
    let mut v___x_6067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_6064_ = leanh::lean_ctor_get(v_inst_6056_, 1);
    leanh::lean_inc(v_toBind_6064_);
    leanh::lean_inc(v_n_6063_);
    leanh::lean_inc_ref(v_inst_6058_);
    leanh::lean_inc_ref(v_inst_6056_);
    v___f_6065_ = leanh::lean_alloc_closure(
        l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_6065_, 0, v_inst_6056_);
    leanh::lean_closure_set(v___f_6065_, 1, v_inst_6058_);
    leanh::lean_closure_set(v___f_6065_, 2, v_inst_6062_);
    leanh::lean_closure_set(v___f_6065_, 3, v_n_6063_);
    v___x_6066_ = 1;
    v___x_6067_ = l_Lean_resolveGlobalName___redArg(
        v_inst_6056_,
        v_inst_6057_,
        v_inst_6058_,
        v_inst_6059_,
        v_inst_6060_,
        v_inst_6061_,
        v_n_6063_,
        v___x_6066_,
    );
    v___x_6068_ = leanh::lean_apply_4(
        v_toBind_6064_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6067_,
        v___f_6065_,
    );
    return v___x_6068_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore(
    mut v_m_6069_: *mut leanh::LeanObject,
    mut v_inst_6070_: *mut leanh::LeanObject,
    mut v_inst_6071_: *mut leanh::LeanObject,
    mut v_inst_6072_: *mut leanh::LeanObject,
    mut v_inst_6073_: *mut leanh::LeanObject,
    mut v_inst_6074_: *mut leanh::LeanObject,
    mut v_inst_6075_: *mut leanh::LeanObject,
    mut v_inst_6076_: *mut leanh::LeanObject,
    mut v_n_6077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6078_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(
        v_inst_6070_,
        v_inst_6071_,
        v_inst_6072_,
        v_inst_6073_,
        v_inst_6074_,
        v_inst_6075_,
        v_inst_6076_,
        v_n_6077_,
    );
    return v___x_6078_;
}
pub unsafe fn l_Lean_ensureNoOverload___redArg___lam__0(
    mut v_declName_6079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6080_ = leanh::lean_box(0);
    v___x_6081_ = l_Lean_mkConst(v_declName_6079_, v___x_6080_);
    return v___x_6081_;
}
pub unsafe fn _init_l_Lean_ensureNoOverload___redArg___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_6084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6084_ = l_Lean_ensureNoOverload___redArg___closed__1;
    v___x_6085_ = l_Lean_stringToMessageData(v___x_6084_);
    return v___x_6085_;
}
pub unsafe fn _init_l_Lean_ensureNoOverload___redArg___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_6087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6087_ = l_Lean_ensureNoOverload___redArg___closed__3;
    v___x_6088_ = l_Lean_stringToMessageData(v___x_6087_);
    return v___x_6088_;
}
pub unsafe fn l_Lean_ensureNoOverload___redArg(
    mut v_inst_6090_: *mut leanh::LeanObject,
    mut v_inst_6091_: *mut leanh::LeanObject,
    mut v_n_6092_: *mut leanh::LeanObject,
    mut v_cs_6093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_6094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_6094_ = leanh::lean_ctor_get(v_inst_6090_, 0);
                v_toPure_6095_ = leanh::lean_ctor_get(v_toApplicative_6094_, 1);
                v___f_6096_ = l_Lean_ensureNoOverload___redArg___closed__0;
                if leanh::lean_obj_tag(v_cs_6093_) == 1 {
                    v_tail_6110_ = leanh::lean_ctor_get(v_cs_6093_, 1);
                    if leanh::lean_obj_tag(v_tail_6110_) == 0 {
                        leanh::lean_inc(v_toPure_6095_);
                        leanh::lean_dec(v_n_6092_);
                        leanh::lean_dec_ref(v_inst_6091_);
                        leanh::lean_dec_ref(v_inst_6090_);
                        v_head_6111_ = leanh::lean_ctor_get(v_cs_6093_, 0);
                        leanh::lean_inc(v_head_6111_);
                        leanh::lean_dec_ref_known(v_cs_6093_, 2);
                        v___x_6112_ = leanh::lean_apply_2(
                            v_toPure_6095_,
                            leanh::lean_box(0),
                            v_head_6111_,
                        );
                        return v___x_6112_;
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6098_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_ensureNoOverload___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_ensureNoOverload___redArg___closed__2_once),
                    _init_l_Lean_ensureNoOverload___redArg___closed__2,
                );
                v___x_6099_ = l_Lean_MessageData_ofName(v_n_6092_);
                v___x_6100_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6100_, 0, v___x_6098_);
                leanh::lean_ctor_set(v___x_6100_, 1, v___x_6099_);
                v___x_6101_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_ensureNoOverload___redArg___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_ensureNoOverload___redArg___closed__4_once),
                    _init_l_Lean_ensureNoOverload___redArg___closed__4,
                );
                v___x_6102_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6102_, 0, v___x_6100_);
                leanh::lean_ctor_set(v___x_6102_, 1, v___x_6101_);
                v___x_6103_ = leanh::lean_box(0);
                v___x_6104_ = l_List_mapTR_loop___redArg(v___f_6096_, v_cs_6093_, v___x_6103_);
                v___x_6105_ = l_Lean_ensureNoOverload___redArg___closed__5;
                v___x_6106_ = l_List_mapTR_loop___redArg(v___x_6105_, v___x_6104_, v___x_6103_);
                v___x_6107_ = l_Lean_MessageData_ofList(v___x_6106_);
                v___x_6108_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6108_, 0, v___x_6102_);
                leanh::lean_ctor_set(v___x_6108_, 1, v___x_6107_);
                v___x_6109_ = l_Lean_throwError___redArg(v_inst_6090_, v_inst_6091_, v___x_6108_);
                return v___x_6109_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ensureNoOverload(
    mut v_m_6113_: *mut leanh::LeanObject,
    mut v_inst_6114_: *mut leanh::LeanObject,
    mut v_inst_6115_: *mut leanh::LeanObject,
    mut v_n_6116_: *mut leanh::LeanObject,
    mut v_cs_6117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6118_ =
        l_Lean_ensureNoOverload___redArg(v_inst_6114_, v_inst_6115_, v_n_6116_, v_cs_6117_);
    return v___x_6118_;
}
pub unsafe fn l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0(
    mut v_inst_6119_: *mut leanh::LeanObject,
    mut v_inst_6120_: *mut leanh::LeanObject,
    mut v_n_6121_: *mut leanh::LeanObject,
    mut v_____do__lift_6122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6123_ = l_Lean_ensureNoOverload___redArg(
        v_inst_6119_,
        v_inst_6120_,
        v_n_6121_,
        v_____do__lift_6122_,
    );
    return v___x_6123_;
}
pub unsafe fn l_Lean_resolveGlobalConstNoOverloadCore___redArg(
    mut v_inst_6124_: *mut leanh::LeanObject,
    mut v_inst_6125_: *mut leanh::LeanObject,
    mut v_inst_6126_: *mut leanh::LeanObject,
    mut v_inst_6127_: *mut leanh::LeanObject,
    mut v_inst_6128_: *mut leanh::LeanObject,
    mut v_inst_6129_: *mut leanh::LeanObject,
    mut v_inst_6130_: *mut leanh::LeanObject,
    mut v_n_6131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_6132_ = leanh::lean_ctor_get(v_inst_6124_, 1);
    leanh::lean_inc(v_toBind_6132_);
    leanh::lean_inc(v_n_6131_);
    leanh::lean_inc_ref(v_inst_6130_);
    leanh::lean_inc_ref(v_inst_6124_);
    v___f_6133_ = leanh::lean_alloc_closure(
        l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_6133_, 0, v_inst_6124_);
    leanh::lean_closure_set(v___f_6133_, 1, v_inst_6130_);
    leanh::lean_closure_set(v___f_6133_, 2, v_n_6131_);
    v___x_6134_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(
        v_inst_6124_,
        v_inst_6125_,
        v_inst_6126_,
        v_inst_6127_,
        v_inst_6128_,
        v_inst_6129_,
        v_inst_6130_,
        v_n_6131_,
    );
    v___x_6135_ = leanh::lean_apply_4(
        v_toBind_6132_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6134_,
        v___f_6133_,
    );
    return v___x_6135_;
}
pub unsafe fn l_Lean_resolveGlobalConstNoOverloadCore(
    mut v_m_6136_: *mut leanh::LeanObject,
    mut v_inst_6137_: *mut leanh::LeanObject,
    mut v_inst_6138_: *mut leanh::LeanObject,
    mut v_inst_6139_: *mut leanh::LeanObject,
    mut v_inst_6140_: *mut leanh::LeanObject,
    mut v_inst_6141_: *mut leanh::LeanObject,
    mut v_inst_6142_: *mut leanh::LeanObject,
    mut v_inst_6143_: *mut leanh::LeanObject,
    mut v_n_6144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6145_ = l_Lean_resolveGlobalConstNoOverloadCore___redArg(
        v_inst_6137_,
        v_inst_6138_,
        v_inst_6139_,
        v_inst_6140_,
        v_inst_6141_,
        v_inst_6142_,
        v_inst_6143_,
        v_n_6144_,
    );
    return v___x_6145_;
}
pub unsafe fn l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(
    mut v_x_6146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6146_) == 1 {
        let mut v_fields_6147_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_fields_6147_ = leanh::lean_ctor_get(v_x_6146_, 1);
        if leanh::lean_obj_tag(v_fields_6147_) == 0 {
            let mut v_n_6148_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6149_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_6148_ = leanh::lean_ctor_get(v_x_6146_, 0);
            leanh::lean_inc(v_n_6148_);
            v___x_6149_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_6149_, 0, v_n_6148_);
            return v___x_6149_;
        } else {
            let mut v___x_6150_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_6150_ = leanh::lean_box(0);
            return v___x_6150_;
        }
    } else {
        let mut v___x_6151_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6151_ = leanh::lean_box(0);
        return v___x_6151_;
    }
}
pub unsafe fn l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed(
    mut v_x_6152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6153_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(v_x_6152_);
    leanh::lean_dec_ref(v_x_6152_);
    return v_res_6153_;
}
pub unsafe fn l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(
    mut v_stx_6154_: *mut leanh::LeanObject,
    mut v_withRef_6155_: *mut leanh::LeanObject,
    mut v___x_6156_: *mut leanh::LeanObject,
    mut v_oldRef_6157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_6158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_6158_ = l_Lean_replaceRef(v_stx_6154_, v_oldRef_6157_);
    v___x_6159_ = leanh::lean_apply_3(
        v_withRef_6155_,
        leanh::lean_box(0),
        v_ref_6158_,
        v___x_6156_,
    );
    return v___x_6159_;
}
pub unsafe fn l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed(
    mut v_stx_6160_: *mut leanh::LeanObject,
    mut v_withRef_6161_: *mut leanh::LeanObject,
    mut v___x_6162_: *mut leanh::LeanObject,
    mut v_oldRef_6163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6164_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(
        v_stx_6160_,
        v_withRef_6161_,
        v___x_6162_,
        v_oldRef_6163_,
    );
    leanh::lean_dec(v_oldRef_6163_);
    leanh::lean_dec(v_stx_6160_);
    return v_res_6164_;
}
pub unsafe fn l_Lean_preprocessSyntaxAndResolve___redArg(
    mut v_inst_6166_: *mut leanh::LeanObject,
    mut v_inst_6167_: *mut leanh::LeanObject,
    mut v_stx_6168_: *mut leanh::LeanObject,
    mut v_k_6169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_stx_6168_) == 3 {
        let mut v_val_6170_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_preresolved_6171_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_pre_6174_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6175_: u8 = 0;
        v_val_6170_ = leanh::lean_ctor_get(v_stx_6168_, 2);
        v_preresolved_6171_ = leanh::lean_ctor_get(v_stx_6168_, 3);
        v___f_6172_ = l_Lean_preprocessSyntaxAndResolve___redArg___closed__0;
        v___x_6173_ = l_Lean_resolveNamespace___redArg___closed__1;
        leanh::lean_inc(v_preresolved_6171_);
        v_pre_6174_ = l_List_filterMapTR_go___redArg(v___f_6172_, v_preresolved_6171_, v___x_6173_);
        v___x_6175_ = l_List_isEmpty___redArg(v_pre_6174_);
        if v___x_6175_ == 0 {
            let mut v_toApplicative_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_6177_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6178_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v_stx_6168_, 4);
            leanh::lean_dec(v_k_6169_);
            leanh::lean_dec_ref(v_inst_6167_);
            v_toApplicative_6176_ = leanh::lean_ctor_get(v_inst_6166_, 0);
            leanh::lean_inc_ref(v_toApplicative_6176_);
            leanh::lean_dec_ref(v_inst_6166_);
            v_toPure_6177_ = leanh::lean_ctor_get(v_toApplicative_6176_, 1);
            leanh::lean_inc(v_toPure_6177_);
            leanh::lean_dec_ref(v_toApplicative_6176_);
            v___x_6178_ =
                leanh::lean_apply_2(v_toPure_6177_, leanh::lean_box(0), v_pre_6174_);
            return v___x_6178_;
        } else {
            let mut v_toMonadRef_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_6180_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_getRef_6181_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_withRef_6182_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6184_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6185_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_pre_6174_);
            v_toMonadRef_6179_ = leanh::lean_ctor_get(v_inst_6167_, 1);
            leanh::lean_inc_ref(v_toMonadRef_6179_);
            leanh::lean_dec_ref(v_inst_6167_);
            v_toBind_6180_ = leanh::lean_ctor_get(v_inst_6166_, 1);
            leanh::lean_inc(v_toBind_6180_);
            leanh::lean_dec_ref(v_inst_6166_);
            v_getRef_6181_ = leanh::lean_ctor_get(v_toMonadRef_6179_, 0);
            leanh::lean_inc(v_getRef_6181_);
            v_withRef_6182_ = leanh::lean_ctor_get(v_toMonadRef_6179_, 1);
            leanh::lean_inc(v_withRef_6182_);
            leanh::lean_dec_ref(v_toMonadRef_6179_);
            leanh::lean_inc(v_val_6170_);
            v___x_6183_ = leanh::lean_apply_1(v_k_6169_, v_val_6170_);
            v___f_6184_ = leanh::lean_alloc_closure(
                l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            leanh::lean_closure_set(v___f_6184_, 0, v_stx_6168_);
            leanh::lean_closure_set(v___f_6184_, 1, v_withRef_6182_);
            leanh::lean_closure_set(v___f_6184_, 2, v___x_6183_);
            v___x_6185_ = leanh::lean_apply_4(
                v_toBind_6180_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_getRef_6181_,
                v___f_6184_,
            );
            return v___x_6185_;
        }
    } else {
        let mut v___x_6186_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6187_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_k_6169_);
        v___x_6186_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_resolveNamespace___redArg___closed__4),
            core::ptr::addr_of_mut!(l_Lean_resolveNamespace___redArg___closed__4_once),
            _init_l_Lean_resolveNamespace___redArg___closed__4,
        );
        v___x_6187_ =
            l_Lean_throwErrorAt___redArg(v_inst_6166_, v_inst_6167_, v_stx_6168_, v___x_6186_);
        return v___x_6187_;
    }
}
pub unsafe fn l_Lean_preprocessSyntaxAndResolve(
    mut v_m_6188_: *mut leanh::LeanObject,
    mut v_inst_6189_: *mut leanh::LeanObject,
    mut v_inst_6190_: *mut leanh::LeanObject,
    mut v_stx_6191_: *mut leanh::LeanObject,
    mut v_k_6192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6193_ = l_Lean_preprocessSyntaxAndResolve___redArg(
        v_inst_6189_,
        v_inst_6190_,
        v_stx_6191_,
        v_k_6192_,
    );
    return v___x_6193_;
}
pub unsafe fn l_Lean_resolveGlobalConst___redArg(
    mut v_inst_6194_: *mut leanh::LeanObject,
    mut v_inst_6195_: *mut leanh::LeanObject,
    mut v_inst_6196_: *mut leanh::LeanObject,
    mut v_inst_6197_: *mut leanh::LeanObject,
    mut v_inst_6198_: *mut leanh::LeanObject,
    mut v_inst_6199_: *mut leanh::LeanObject,
    mut v_inst_6200_: *mut leanh::LeanObject,
    mut v_stx_6201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_6200_);
    leanh::lean_inc_ref(v_inst_6194_);
    v___x_6202_ = leanh::lean_alloc_closure(
        l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___x_6202_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_6202_, 1, v_inst_6194_);
    leanh::lean_closure_set(v___x_6202_, 2, v_inst_6195_);
    leanh::lean_closure_set(v___x_6202_, 3, v_inst_6196_);
    leanh::lean_closure_set(v___x_6202_, 4, v_inst_6197_);
    leanh::lean_closure_set(v___x_6202_, 5, v_inst_6198_);
    leanh::lean_closure_set(v___x_6202_, 6, v_inst_6199_);
    leanh::lean_closure_set(v___x_6202_, 7, v_inst_6200_);
    v___x_6203_ = l_Lean_preprocessSyntaxAndResolve___redArg(
        v_inst_6194_,
        v_inst_6200_,
        v_stx_6201_,
        v___x_6202_,
    );
    return v___x_6203_;
}
pub unsafe fn l_Lean_resolveGlobalConst(
    mut v_m_6204_: *mut leanh::LeanObject,
    mut v_inst_6205_: *mut leanh::LeanObject,
    mut v_inst_6206_: *mut leanh::LeanObject,
    mut v_inst_6207_: *mut leanh::LeanObject,
    mut v_inst_6208_: *mut leanh::LeanObject,
    mut v_inst_6209_: *mut leanh::LeanObject,
    mut v_inst_6210_: *mut leanh::LeanObject,
    mut v_inst_6211_: *mut leanh::LeanObject,
    mut v_stx_6212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6213_ = l_Lean_resolveGlobalConst___redArg(
        v_inst_6205_,
        v_inst_6206_,
        v_inst_6207_,
        v_inst_6208_,
        v_inst_6209_,
        v_inst_6210_,
        v_inst_6211_,
        v_stx_6212_,
    );
    return v___x_6213_;
}
pub unsafe fn _init_l_Lean_ensureNonAmbiguous___redArg___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_6215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6215_ = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2;
    v___x_6216_ = leanh::lean_unsigned_to_nat(11);
    v___x_6217_ = leanh::lean_unsigned_to_nat(429);
    v___x_6218_ = l_Lean_ensureNonAmbiguous___redArg___closed__0;
    v___x_6219_ = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0;
    v___x_6220_ = l_mkPanicMessageWithDecl(
        v___x_6219_,
        v___x_6218_,
        v___x_6217_,
        v___x_6216_,
        v___x_6215_,
    );
    return v___x_6220_;
}
pub unsafe fn l_Lean_ensureNonAmbiguous___redArg(
    mut v_inst_6224_: *mut leanh::LeanObject,
    mut v_inst_6225_: *mut leanh::LeanObject,
    mut v_id_6226_: *mut leanh::LeanObject,
    mut v_cs_6227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_cs_6227_) == 0 {
        let mut v___x_6228_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6229_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6230_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6231_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_id_6226_);
        leanh::lean_dec_ref(v_inst_6225_);
        v___x_6228_ = leanh::lean_box(0);
        v___x_6229_ = l_instInhabitedOfMonad___redArg(v_inst_6224_, v___x_6228_);
        v___x_6230_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_ensureNonAmbiguous___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Lean_ensureNonAmbiguous___redArg___closed__1_once),
            _init_l_Lean_ensureNonAmbiguous___redArg___closed__1,
        );
        v___x_6231_ = l_panic___redArg(v___x_6229_, v___x_6230_);
        leanh::lean_dec(v___x_6229_);
        return v___x_6231_;
    } else {
        let mut v_tail_6232_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_6232_ = leanh::lean_ctor_get(v_cs_6227_, 1);
        if leanh::lean_obj_tag(v_tail_6232_) == 0 {
            let mut v_toApplicative_6233_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_6235_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6236_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_6233_ = leanh::lean_ctor_get(v_inst_6224_, 0);
            leanh::lean_inc_ref(v_toApplicative_6233_);
            leanh::lean_dec(v_id_6226_);
            leanh::lean_dec_ref(v_inst_6225_);
            leanh::lean_dec_ref(v_inst_6224_);
            v_toPure_6234_ = leanh::lean_ctor_get(v_toApplicative_6233_, 1);
            leanh::lean_inc(v_toPure_6234_);
            leanh::lean_dec_ref(v_toApplicative_6233_);
            v_head_6235_ = leanh::lean_ctor_get(v_cs_6227_, 0);
            leanh::lean_inc(v_head_6235_);
            leanh::lean_dec_ref_known(v_cs_6227_, 2);
            v___x_6236_ =
                leanh::lean_apply_2(v_toPure_6234_, leanh::lean_box(0), v_head_6235_);
            return v___x_6236_;
        } else {
            let mut v___f_6237_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6238_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6239_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6240_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6241_: u8 = 0;
            let mut v___x_6242_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6243_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6244_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6245_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6246_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6247_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6248_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6249_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6250_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6251_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6252_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6253_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6254_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6255_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___f_6237_ = l_Lean_ensureNoOverload___redArg___closed__0;
            v___x_6238_ = l_Lean_ensureNonAmbiguous___redArg___closed__2;
            v___x_6239_ = l_Lean_ensureNonAmbiguous___redArg___closed__3;
            v___x_6240_ = leanh::lean_box(0);
            v___x_6241_ = 0;
            leanh::lean_inc(v_id_6226_);
            v___x_6242_ = l_Lean_Syntax_formatStx(v_id_6226_, v___x_6240_, v___x_6241_);
            v___x_6243_ = l_Std_Format_defWidth;
            v___x_6244_ = leanh::lean_unsigned_to_nat(0);
            v___x_6245_ = l_Std_Format_pretty(v___x_6242_, v___x_6243_, v___x_6244_, v___x_6244_);
            v___x_6246_ = lean_string_append(v___x_6239_, v___x_6245_);
            leanh::lean_dec_ref(v___x_6245_);
            v___x_6247_ = l_Lean_ensureNonAmbiguous___redArg___closed__4;
            v___x_6248_ = lean_string_append(v___x_6246_, v___x_6247_);
            v___x_6249_ = leanh::lean_box(0);
            v___x_6250_ = l_List_mapTR_loop___redArg(v___f_6237_, v_cs_6227_, v___x_6249_);
            v___x_6251_ = l_List_toString___redArg(v___x_6238_, v___x_6250_);
            v___x_6252_ = lean_string_append(v___x_6248_, v___x_6251_);
            leanh::lean_dec_ref(v___x_6251_);
            v___x_6253_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_6253_, 0, v___x_6252_);
            v___x_6254_ = l_Lean_MessageData_ofFormat(v___x_6253_);
            v___x_6255_ =
                l_Lean_throwErrorAt___redArg(v_inst_6224_, v_inst_6225_, v_id_6226_, v___x_6254_);
            return v___x_6255_;
        }
    }
}
pub unsafe fn l_Lean_ensureNonAmbiguous(
    mut v_m_6256_: *mut leanh::LeanObject,
    mut v_inst_6257_: *mut leanh::LeanObject,
    mut v_inst_6258_: *mut leanh::LeanObject,
    mut v_id_6259_: *mut leanh::LeanObject,
    mut v_cs_6260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6261_ =
        l_Lean_ensureNonAmbiguous___redArg(v_inst_6257_, v_inst_6258_, v_id_6259_, v_cs_6260_);
    return v___x_6261_;
}
pub unsafe fn l_Lean_resolveGlobalConstNoOverload___redArg___lam__0(
    mut v_inst_6262_: *mut leanh::LeanObject,
    mut v_inst_6263_: *mut leanh::LeanObject,
    mut v_id_6264_: *mut leanh::LeanObject,
    mut v_____do__lift_6265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6266_ = l_Lean_ensureNonAmbiguous___redArg(
        v_inst_6262_,
        v_inst_6263_,
        v_id_6264_,
        v_____do__lift_6265_,
    );
    return v___x_6266_;
}
pub unsafe fn l_Lean_resolveGlobalConstNoOverload___redArg(
    mut v_inst_6267_: *mut leanh::LeanObject,
    mut v_inst_6268_: *mut leanh::LeanObject,
    mut v_inst_6269_: *mut leanh::LeanObject,
    mut v_inst_6270_: *mut leanh::LeanObject,
    mut v_inst_6271_: *mut leanh::LeanObject,
    mut v_inst_6272_: *mut leanh::LeanObject,
    mut v_inst_6273_: *mut leanh::LeanObject,
    mut v_id_6274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_6275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_6275_ = leanh::lean_ctor_get(v_inst_6267_, 1);
    leanh::lean_inc(v_toBind_6275_);
    leanh::lean_inc(v_id_6274_);
    leanh::lean_inc_ref(v_inst_6273_);
    leanh::lean_inc_ref(v_inst_6267_);
    v___f_6276_ = leanh::lean_alloc_closure(
        l_Lean_resolveGlobalConstNoOverload___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_6276_, 0, v_inst_6267_);
    leanh::lean_closure_set(v___f_6276_, 1, v_inst_6273_);
    leanh::lean_closure_set(v___f_6276_, 2, v_id_6274_);
    v___x_6277_ = l_Lean_resolveGlobalConst___redArg(
        v_inst_6267_,
        v_inst_6268_,
        v_inst_6269_,
        v_inst_6270_,
        v_inst_6271_,
        v_inst_6272_,
        v_inst_6273_,
        v_id_6274_,
    );
    v___x_6278_ = leanh::lean_apply_4(
        v_toBind_6275_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6277_,
        v___f_6276_,
    );
    return v___x_6278_;
}
pub unsafe fn l_Lean_resolveGlobalConstNoOverload(
    mut v_m_6279_: *mut leanh::LeanObject,
    mut v_inst_6280_: *mut leanh::LeanObject,
    mut v_inst_6281_: *mut leanh::LeanObject,
    mut v_inst_6282_: *mut leanh::LeanObject,
    mut v_inst_6283_: *mut leanh::LeanObject,
    mut v_inst_6284_: *mut leanh::LeanObject,
    mut v_inst_6285_: *mut leanh::LeanObject,
    mut v_inst_6286_: *mut leanh::LeanObject,
    mut v_id_6287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6288_ = l_Lean_resolveGlobalConstNoOverload___redArg(
        v_inst_6280_,
        v_inst_6281_,
        v_inst_6282_,
        v_inst_6283_,
        v_inst_6284_,
        v_inst_6285_,
        v_inst_6286_,
        v_id_6287_,
    );
    return v___x_6288_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(
    mut v___f_6289_: *mut leanh::LeanObject,
    mut v___f_6290_: *mut leanh::LeanObject,
    mut v_globalDeclFoundNext_6291_: u8,
    mut v_globalDeclFound_6292_: u8,
    mut v_r_6293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: u8 = 0;
    v___x_6294_ = leanh::lean_box(0);
    v_r_6295_ = l_List_filterTR_loop___redArg(v___f_6289_, v_r_6293_, v___x_6294_);
    v___x_6296_ = l_List_isEmpty___redArg(v_r_6295_);
    leanh::lean_dec(v_r_6295_);
    if v___x_6296_ == 0 {
        let mut v___x_6297_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6298_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6299_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6297_ = leanh::lean_box(0);
        v___x_6298_ = leanh::lean_box((v_globalDeclFoundNext_6291_) as usize);
        v___x_6299_ = leanh::lean_apply_2(v___f_6290_, v___x_6297_, v___x_6298_);
        return v___x_6299_;
    } else {
        let mut v___x_6300_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6301_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6302_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6300_ = leanh::lean_box(0);
        v___x_6301_ = leanh::lean_box((v_globalDeclFound_6292_) as usize);
        v___x_6302_ = leanh::lean_apply_2(v___f_6290_, v___x_6300_, v___x_6301_);
        return v___x_6302_;
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed(
    mut v___f_6303_: *mut leanh::LeanObject,
    mut v___f_6304_: *mut leanh::LeanObject,
    mut v_globalDeclFoundNext_6305_: *mut leanh::LeanObject,
    mut v_globalDeclFound_6306_: *mut leanh::LeanObject,
    mut v_r_6307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_globalDeclFoundNext_boxed_6308_: u8 = 0;
    let mut v_globalDeclFound_boxed_6309_: u8 = 0;
    let mut v_res_6310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_globalDeclFoundNext_boxed_6308_ =
        (leanh::lean_unbox(v_globalDeclFoundNext_6305_) as u8);
    v_globalDeclFound_boxed_6309_ = (leanh::lean_unbox(v_globalDeclFound_6306_) as u8);
    v_res_6310_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(
        v___f_6303_,
        v___f_6304_,
        v_globalDeclFoundNext_boxed_6308_,
        v_globalDeclFound_boxed_6309_,
        v_r_6307_,
    );
    return v_res_6310_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed(
    mut v_str_6311_: *mut leanh::LeanObject,
    mut v_projs_6312_: *mut leanh::LeanObject,
    mut v_inst_6313_: *mut leanh::LeanObject,
    mut v_inst_6314_: *mut leanh::LeanObject,
    mut v_inst_6315_: *mut leanh::LeanObject,
    mut v_inst_6316_: *mut leanh::LeanObject,
    mut v_inst_6317_: *mut leanh::LeanObject,
    mut v_inst_6318_: *mut leanh::LeanObject,
    mut v_view_6319_: *mut leanh::LeanObject,
    mut v_findLocalDecl_x3f_6320_: *mut leanh::LeanObject,
    mut v_pre_6321_: *mut leanh::LeanObject,
    mut v_____r_6322_: *mut leanh::LeanObject,
    mut v_globalDeclFoundNext_6323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_globalDeclFoundNext_boxed_6324_: u8 = 0;
    let mut v_res_6325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_globalDeclFoundNext_boxed_6324_ =
        (leanh::lean_unbox(v_globalDeclFoundNext_6323_) as u8);
    v_res_6325_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(
        v_str_6311_,
        v_projs_6312_,
        v_inst_6313_,
        v_inst_6314_,
        v_inst_6315_,
        v_inst_6316_,
        v_inst_6317_,
        v_inst_6318_,
        v_view_6319_,
        v_findLocalDecl_x3f_6320_,
        v_pre_6321_,
        v_____r_6322_,
        v_globalDeclFoundNext_boxed_6324_,
    );
    return v_res_6325_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(
    mut v_inst_6326_: *mut leanh::LeanObject,
    mut v_inst_6327_: *mut leanh::LeanObject,
    mut v_inst_6328_: *mut leanh::LeanObject,
    mut v_inst_6329_: *mut leanh::LeanObject,
    mut v_inst_6330_: *mut leanh::LeanObject,
    mut v_inst_6331_: *mut leanh::LeanObject,
    mut v_view_6332_: *mut leanh::LeanObject,
    mut v_findLocalDecl_x3f_6333_: *mut leanh::LeanObject,
    mut v_n_6334_: *mut leanh::LeanObject,
    mut v_projs_6335_: *mut leanh::LeanObject,
    mut v_globalDeclFound_6336_: u8,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_6337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_imported_6338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_6339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_givenNameView_6344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6346_: u8 = 0;
    let mut v___x_6347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_6349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_globalDeclFoundNext_6352_: u8 = 0;
    let mut v___x_6353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6365_: u8 = 0;
    let mut v_val_6366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6369_: u8 = 0;
    let mut v___x_6370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6378_: u8 = 0;
    let mut v_isSharedCheck_6379_: u8 = 0;
    let mut v_unused_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: u8 = 0;
    let mut v___x_6383_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_6337_ = leanh::lean_ctor_get(v_inst_6326_, 0);
                v_imported_6338_ = leanh::lean_ctor_get(v_view_6332_, 1);
                v_ctx_6339_ = leanh::lean_ctor_get(v_view_6332_, 2);
                v_scopes_6340_ = leanh::lean_ctor_get(v_view_6332_, 3);
                v_toBind_6341_ = leanh::lean_ctor_get(v_inst_6326_, 1);
                v_toPure_6342_ = leanh::lean_ctor_get(v_toApplicative_6337_, 1);
                v___f_6343_ = l_Lean_filterFieldList___redArg___closed__0;
                leanh::lean_inc(v_scopes_6340_);
                leanh::lean_inc(v_ctx_6339_);
                leanh::lean_inc(v_imported_6338_);
                leanh::lean_inc(v_n_6334_);
                v_givenNameView_6344_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v_givenNameView_6344_, 0, v_n_6334_);
                leanh::lean_ctor_set(v_givenNameView_6344_, 1, v_imported_6338_);
                leanh::lean_ctor_set(v_givenNameView_6344_, 2, v_ctx_6339_);
                leanh::lean_ctor_set(v_givenNameView_6344_, 3, v_scopes_6340_);
                if v_globalDeclFound_6336_ == 0 {
                    v___y_6346_ = v_globalDeclFound_6336_;
                    state = 1;
                    continue;
                } else {
                    v___x_6382_ = l_List_isEmpty___redArg(v_projs_6335_);
                    if v___x_6382_ == 0 {
                        v___y_6346_ = v_globalDeclFound_6336_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6383_ = 0;
                        v___y_6346_ = v___x_6383_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6347_ = leanh::lean_box((v___y_6346_) as usize);
                leanh::lean_inc_ref(v_findLocalDecl_x3f_6333_);
                leanh::lean_inc_ref(v_givenNameView_6344_);
                v___x_6348_ = leanh::lean_apply_2(
                    v_findLocalDecl_x3f_6333_,
                    v_givenNameView_6344_,
                    v___x_6347_,
                );
                if leanh::lean_obj_tag(v___x_6348_) == 0 {
                    if leanh::lean_obj_tag(v_n_6334_) == 1 {
                        v_pre_6349_ = leanh::lean_ctor_get(v_n_6334_, 0);
                        leanh::lean_inc_n(v_pre_6349_, 2);
                        v_str_6350_ = leanh::lean_ctor_get(v_n_6334_, 1);
                        leanh::lean_inc_ref_n(v_str_6350_, 2);
                        leanh::lean_dec_ref_known(v_n_6334_, 2);
                        leanh::lean_inc_ref(v_findLocalDecl_x3f_6333_);
                        leanh::lean_inc_ref(v_view_6332_);
                        leanh::lean_inc(v_inst_6331_);
                        leanh::lean_inc_ref(v_inst_6330_);
                        leanh::lean_inc(v_inst_6329_);
                        leanh::lean_inc_ref(v_inst_6328_);
                        leanh::lean_inc_ref(v_inst_6327_);
                        leanh::lean_inc_ref(v_inst_6326_);
                        leanh::lean_inc(v_projs_6335_);
                        v___f_6351_ = leanh::lean_alloc_closure(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed as *mut core::ffi::c_void, 13, 11);
                        leanh::lean_closure_set(v___f_6351_, 0, v_str_6350_);
                        leanh::lean_closure_set(v___f_6351_, 1, v_projs_6335_);
                        leanh::lean_closure_set(v___f_6351_, 2, v_inst_6326_);
                        leanh::lean_closure_set(v___f_6351_, 3, v_inst_6327_);
                        leanh::lean_closure_set(v___f_6351_, 4, v_inst_6328_);
                        leanh::lean_closure_set(v___f_6351_, 5, v_inst_6329_);
                        leanh::lean_closure_set(v___f_6351_, 6, v_inst_6330_);
                        leanh::lean_closure_set(v___f_6351_, 7, v_inst_6331_);
                        leanh::lean_closure_set(v___f_6351_, 8, v_view_6332_);
                        leanh::lean_closure_set(v___f_6351_, 9, v_findLocalDecl_x3f_6333_);
                        leanh::lean_closure_set(v___f_6351_, 10, v_pre_6349_);
                        if v_globalDeclFound_6336_ == 0 {
                            leanh::lean_inc(v_toBind_6341_);
                            leanh::lean_dec_ref(v_str_6350_);
                            leanh::lean_dec(v_pre_6349_);
                            leanh::lean_dec(v_projs_6335_);
                            leanh::lean_dec_ref(v_findLocalDecl_x3f_6333_);
                            leanh::lean_dec_ref(v_view_6332_);
                            v_globalDeclFoundNext_6352_ = 1;
                            v___x_6353_ =
                                leanh::lean_box((v_globalDeclFoundNext_6352_) as usize);
                            v___x_6354_ =
                                leanh::lean_box((v_globalDeclFound_6336_) as usize);
                            v___f_6355_ = leanh::lean_alloc_closure(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 4);
                            leanh::lean_closure_set(v___f_6355_, 0, v___f_6343_);
                            leanh::lean_closure_set(v___f_6355_, 1, v___f_6351_);
                            leanh::lean_closure_set(v___f_6355_, 2, v___x_6353_);
                            leanh::lean_closure_set(v___f_6355_, 3, v___x_6354_);
                            v___x_6356_ = l_Lean_MacroScopesView_review(v_givenNameView_6344_);
                            v___x_6357_ = l_Lean_resolveGlobalName___redArg(
                                v_inst_6326_,
                                v_inst_6327_,
                                v_inst_6328_,
                                v_inst_6329_,
                                v_inst_6330_,
                                v_inst_6331_,
                                v___x_6356_,
                                v_globalDeclFound_6336_,
                            );
                            v___x_6358_ = leanh::lean_apply_4(
                                v_toBind_6341_,
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_6357_,
                                v___f_6355_,
                            );
                            return v___x_6358_;
                        } else {
                            leanh::lean_dec_ref(v___f_6351_);
                            leanh::lean_dec_ref_known(v_givenNameView_6344_, 4);
                            v___x_6359_ = leanh::lean_box(0);
                            v___x_6360_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_6350_, v_projs_6335_, v_inst_6326_, v_inst_6327_, v_inst_6328_, v_inst_6329_, v_inst_6330_, v_inst_6331_, v_view_6332_, v_findLocalDecl_x3f_6333_, v_pre_6349_, v___x_6359_, v_globalDeclFound_6336_);
                            return v___x_6360_;
                        }
                    } else {
                        leanh::lean_inc(v_toPure_6342_);
                        leanh::lean_dec_ref_known(v_givenNameView_6344_, 4);
                        leanh::lean_dec(v_projs_6335_);
                        leanh::lean_dec(v_n_6334_);
                        leanh::lean_dec_ref(v_findLocalDecl_x3f_6333_);
                        leanh::lean_dec_ref(v_view_6332_);
                        leanh::lean_dec(v_inst_6331_);
                        leanh::lean_dec_ref(v_inst_6330_);
                        leanh::lean_dec(v_inst_6329_);
                        leanh::lean_dec_ref(v_inst_6328_);
                        leanh::lean_dec_ref(v_inst_6327_);
                        leanh::lean_dec_ref(v_inst_6326_);
                        v___x_6361_ = leanh::lean_box(0);
                        v___x_6362_ = leanh::lean_apply_2(
                            v_toPure_6342_,
                            leanh::lean_box(0),
                            v___x_6361_,
                        );
                        return v___x_6362_;
                    }
                } else {
                    leanh::lean_inc(v_toPure_6342_);
                    leanh::lean_dec_ref_known(v_givenNameView_6344_, 4);
                    leanh::lean_dec(v_n_6334_);
                    leanh::lean_dec_ref(v_findLocalDecl_x3f_6333_);
                    leanh::lean_dec_ref(v_view_6332_);
                    leanh::lean_dec(v_inst_6331_);
                    leanh::lean_dec_ref(v_inst_6330_);
                    leanh::lean_dec(v_inst_6329_);
                    leanh::lean_dec_ref(v_inst_6328_);
                    leanh::lean_dec_ref(v_inst_6327_);
                    v_isSharedCheck_6379_ = (!leanh::lean_is_exclusive(v_inst_6326_)) as u8;
                    if v_isSharedCheck_6379_ == 0 {
                        v_unused_6380_ = leanh::lean_ctor_get(v_inst_6326_, 1);
                        leanh::lean_dec(v_unused_6380_);
                        v_unused_6381_ = leanh::lean_ctor_get(v_inst_6326_, 0);
                        leanh::lean_dec(v_unused_6381_);
                        v___x_6364_ = v_inst_6326_;
                        v_isShared_6365_ = v_isSharedCheck_6379_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_inst_6326_);
                        v___x_6364_ = leanh::lean_box(0);
                        v_isShared_6365_ = v_isSharedCheck_6379_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_val_6366_ = leanh::lean_ctor_get(v___x_6348_, 0);
                v_isSharedCheck_6378_ = (!leanh::lean_is_exclusive(v___x_6348_)) as u8;
                if v_isSharedCheck_6378_ == 0 {
                    v___x_6368_ = v___x_6348_;
                    v_isShared_6369_ = v_isSharedCheck_6378_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_val_6366_);
                    leanh::lean_dec(v___x_6348_);
                    v___x_6368_ = leanh::lean_box(0);
                    v_isShared_6369_ = v_isSharedCheck_6378_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6370_ = l_Lean_LocalDecl_toExpr(v_val_6366_);
                if v_isShared_6365_ == 0 {
                    leanh::lean_ctor_set(v___x_6364_, 1, v_projs_6335_);
                    leanh::lean_ctor_set(v___x_6364_, 0, v___x_6370_);
                    v___x_6372_ = v___x_6364_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6377_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6377_, 0, v___x_6370_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6377_, 1, v_projs_6335_);
                    v___x_6372_ = v_reuseFailAlloc_6377_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6369_ == 0 {
                    leanh::lean_ctor_set(v___x_6368_, 0, v___x_6372_);
                    v___x_6374_ = v___x_6368_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6376_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6376_, 0, v___x_6372_);
                    v___x_6374_ = v_reuseFailAlloc_6376_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6375_ = leanh::lean_apply_2(
                    v_toPure_6342_,
                    leanh::lean_box(0),
                    v___x_6374_,
                );
                return v___x_6375_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(
    mut v_str_6384_: *mut leanh::LeanObject,
    mut v_projs_6385_: *mut leanh::LeanObject,
    mut v_inst_6386_: *mut leanh::LeanObject,
    mut v_inst_6387_: *mut leanh::LeanObject,
    mut v_inst_6388_: *mut leanh::LeanObject,
    mut v_inst_6389_: *mut leanh::LeanObject,
    mut v_inst_6390_: *mut leanh::LeanObject,
    mut v_inst_6391_: *mut leanh::LeanObject,
    mut v_view_6392_: *mut leanh::LeanObject,
    mut v_findLocalDecl_x3f_6393_: *mut leanh::LeanObject,
    mut v_pre_6394_: *mut leanh::LeanObject,
    mut v_____r_6395_: *mut leanh::LeanObject,
    mut v_globalDeclFoundNext_6396_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_6397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6397_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6397_, 0, v_str_6384_);
    leanh::lean_ctor_set(v___x_6397_, 1, v_projs_6385_);
    v___x_6398_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(
        v_inst_6386_,
        v_inst_6387_,
        v_inst_6388_,
        v_inst_6389_,
        v_inst_6390_,
        v_inst_6391_,
        v_view_6392_,
        v_findLocalDecl_x3f_6393_,
        v_pre_6394_,
        v___x_6397_,
        v_globalDeclFoundNext_6396_,
    );
    return v___x_6398_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___boxed(
    mut v_inst_6399_: *mut leanh::LeanObject,
    mut v_inst_6400_: *mut leanh::LeanObject,
    mut v_inst_6401_: *mut leanh::LeanObject,
    mut v_inst_6402_: *mut leanh::LeanObject,
    mut v_inst_6403_: *mut leanh::LeanObject,
    mut v_inst_6404_: *mut leanh::LeanObject,
    mut v_view_6405_: *mut leanh::LeanObject,
    mut v_findLocalDecl_x3f_6406_: *mut leanh::LeanObject,
    mut v_n_6407_: *mut leanh::LeanObject,
    mut v_projs_6408_: *mut leanh::LeanObject,
    mut v_globalDeclFound_6409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_globalDeclFound_boxed_6410_: u8 = 0;
    let mut v_res_6411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_globalDeclFound_boxed_6410_ = (leanh::lean_unbox(v_globalDeclFound_6409_) as u8);
    v_res_6411_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(
        v_inst_6399_,
        v_inst_6400_,
        v_inst_6401_,
        v_inst_6402_,
        v_inst_6403_,
        v_inst_6404_,
        v_view_6405_,
        v_findLocalDecl_x3f_6406_,
        v_n_6407_,
        v_projs_6408_,
        v_globalDeclFound_boxed_6410_,
    );
    return v_res_6411_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(
    mut v_m_6412_: *mut leanh::LeanObject,
    mut v_inst_6413_: *mut leanh::LeanObject,
    mut v_inst_6414_: *mut leanh::LeanObject,
    mut v_inst_6415_: *mut leanh::LeanObject,
    mut v_inst_6416_: *mut leanh::LeanObject,
    mut v_inst_6417_: *mut leanh::LeanObject,
    mut v_inst_6418_: *mut leanh::LeanObject,
    mut v_view_6419_: *mut leanh::LeanObject,
    mut v_findLocalDecl_x3f_6420_: *mut leanh::LeanObject,
    mut v_n_6421_: *mut leanh::LeanObject,
    mut v_projs_6422_: *mut leanh::LeanObject,
    mut v_globalDeclFound_6423_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_6424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6424_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(
        v_inst_6413_,
        v_inst_6414_,
        v_inst_6415_,
        v_inst_6416_,
        v_inst_6417_,
        v_inst_6418_,
        v_view_6419_,
        v_findLocalDecl_x3f_6420_,
        v_n_6421_,
        v_projs_6422_,
        v_globalDeclFound_6423_,
    );
    return v___x_6424_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___boxed(
    mut v_m_6425_: *mut leanh::LeanObject,
    mut v_inst_6426_: *mut leanh::LeanObject,
    mut v_inst_6427_: *mut leanh::LeanObject,
    mut v_inst_6428_: *mut leanh::LeanObject,
    mut v_inst_6429_: *mut leanh::LeanObject,
    mut v_inst_6430_: *mut leanh::LeanObject,
    mut v_inst_6431_: *mut leanh::LeanObject,
    mut v_view_6432_: *mut leanh::LeanObject,
    mut v_findLocalDecl_x3f_6433_: *mut leanh::LeanObject,
    mut v_n_6434_: *mut leanh::LeanObject,
    mut v_projs_6435_: *mut leanh::LeanObject,
    mut v_globalDeclFound_6436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_globalDeclFound_boxed_6437_: u8 = 0;
    let mut v_res_6438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_globalDeclFound_boxed_6437_ = (leanh::lean_unbox(v_globalDeclFound_6436_) as u8);
    v_res_6438_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(
        v_m_6425_,
        v_inst_6426_,
        v_inst_6427_,
        v_inst_6428_,
        v_inst_6429_,
        v_inst_6430_,
        v_inst_6431_,
        v_view_6432_,
        v_findLocalDecl_x3f_6433_,
        v_n_6434_,
        v_projs_6435_,
        v_globalDeclFound_boxed_6437_,
    );
    return v_res_6438_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(
    mut v_localDecl_6439_: *mut leanh::LeanObject,
    mut v_givenNameView_6440_: *mut leanh::LeanObject,
    mut v_fullDeclName_6441_: *mut leanh::LeanObject,
    mut v_ns_6442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_6443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_imported_6444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_6445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6450_: u8 = 0;
    let mut v_pre_6451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_6443_ = leanh::lean_ctor_get(v_givenNameView_6440_, 0);
                v_imported_6444_ = leanh::lean_ctor_get(v_givenNameView_6440_, 1);
                v_ctx_6445_ = leanh::lean_ctor_get(v_givenNameView_6440_, 2);
                v_scopes_6446_ = leanh::lean_ctor_get(v_givenNameView_6440_, 3);
                leanh::lean_inc(v_name_6443_);
                leanh::lean_inc(v_ns_6442_);
                v___x_6447_ = l_Lean_Name_append(v_ns_6442_, v_name_6443_);
                leanh::lean_inc(v_scopes_6446_);
                leanh::lean_inc(v_ctx_6445_);
                leanh::lean_inc(v_imported_6444_);
                v___x_6448_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_6448_, 0, v___x_6447_);
                leanh::lean_ctor_set(v___x_6448_, 1, v_imported_6444_);
                leanh::lean_ctor_set(v___x_6448_, 2, v_ctx_6445_);
                leanh::lean_ctor_set(v___x_6448_, 3, v_scopes_6446_);
                v___x_6449_ = l_Lean_MacroScopesView_review(v___x_6448_);
                v___x_6450_ = lean_name_eq(v___x_6449_, v_fullDeclName_6441_);
                leanh::lean_dec(v___x_6449_);
                if v___x_6450_ == 0 {
                    if leanh::lean_obj_tag(v_ns_6442_) == 1 {
                        v_pre_6451_ = leanh::lean_ctor_get(v_ns_6442_, 0);
                        leanh::lean_inc(v_pre_6451_);
                        leanh::lean_dec_ref_known(v_ns_6442_, 2);
                        v_ns_6442_ = v_pre_6451_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_ns_6442_);
                        leanh::lean_dec_ref(v_givenNameView_6440_);
                        leanh::lean_dec_ref(v_localDecl_6439_);
                        v___x_6453_ = leanh::lean_box(0);
                        return v___x_6453_;
                    }
                } else {
                    leanh::lean_dec(v_ns_6442_);
                    leanh::lean_dec_ref(v_givenNameView_6440_);
                    v___x_6454_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6454_, 0, v_localDecl_6439_);
                    return v___x_6454_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_resolveLocalName_go___boxed(
    mut v_localDecl_6455_: *mut leanh::LeanObject,
    mut v_givenNameView_6456_: *mut leanh::LeanObject,
    mut v_fullDeclName_6457_: *mut leanh::LeanObject,
    mut v_ns_6458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6459_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(
        v_localDecl_6455_,
        v_givenNameView_6456_,
        v_fullDeclName_6457_,
        v_ns_6458_,
    );
    leanh::lean_dec(v_fullDeclName_6457_);
    return v_res_6459_;
}
pub unsafe fn l_Lean_resolveLocalName___redArg___lam__0(
    mut v_localDecl_6460_: *mut leanh::LeanObject,
    mut v_givenName_6461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: u8 = 0;
    v___x_6462_ = l_Lean_LocalDecl_userName(v_localDecl_6460_);
    v___x_6463_ = lean_name_eq(v___x_6462_, v_givenName_6461_);
    leanh::lean_dec(v___x_6462_);
    if v___x_6463_ == 0 {
        let mut v___x_6464_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_localDecl_6460_);
        v___x_6464_ = leanh::lean_box(0);
        return v___x_6464_;
    } else {
        let mut v___x_6465_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6465_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6465_, 0, v_localDecl_6460_);
        return v___x_6465_;
    }
}
pub unsafe fn l_Lean_resolveLocalName___redArg___lam__0___boxed(
    mut v_localDecl_6466_: *mut leanh::LeanObject,
    mut v_givenName_6467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6468_ = l_Lean_resolveLocalName___redArg___lam__0(v_localDecl_6466_, v_givenName_6467_);
    leanh::lean_dec(v_givenName_6467_);
    return v_res_6468_;
}
pub unsafe fn l_Lean_resolveLocalName___redArg___lam__1(
    mut v_matchLocalDecl_x3f_6469_: *mut leanh::LeanObject,
    mut v_givenName_6470_: *mut leanh::LeanObject,
    mut v_skipAuxDecl_6471_: u8,
    mut v___f_6472_: *mut leanh::LeanObject,
    mut v_auxDeclToFullName_6473_: *mut leanh::LeanObject,
    mut v_currNamespace_6474_: *mut leanh::LeanObject,
    mut v_givenNameView_6475_: *mut leanh::LeanObject,
    mut v_x_6476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_6477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6478_: u8 = 0;
    let mut v___x_6479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fullDeclView_6484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_imported_6487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_6488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6492_: u8 = 0;
    let mut v_fullDeclView_6494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fullDeclName_6495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: u8 = 0;
    let mut v___x_6497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localDeclNameView_6499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: u8 = 0;
    let mut v___x_6501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: u8 = 0;
    let mut v___x_6503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6505_: u8 = 0;
    let mut v_unused_6506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_6507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6476_) == 0 {
                    leanh::lean_dec_ref(v_givenNameView_6475_);
                    leanh::lean_dec(v_currNamespace_6474_);
                    leanh::lean_dec(v_auxDeclToFullName_6473_);
                    leanh::lean_dec_ref(v___f_6472_);
                    leanh::lean_dec(v_givenName_6470_);
                    leanh::lean_dec_ref(v_matchLocalDecl_x3f_6469_);
                    return v_x_6476_;
                } else {
                    v_val_6477_ = leanh::lean_ctor_get(v_x_6476_, 0);
                    v___x_6478_ = l_Lean_LocalDecl_isAuxDecl(v_val_6477_);
                    if v___x_6478_ == 0 {
                        leanh::lean_inc(v_val_6477_);
                        leanh::lean_dec_ref_known(v_x_6476_, 1);
                        leanh::lean_dec_ref(v_givenNameView_6475_);
                        leanh::lean_dec(v_currNamespace_6474_);
                        leanh::lean_dec(v_auxDeclToFullName_6473_);
                        leanh::lean_dec_ref(v___f_6472_);
                        v___x_6479_ = leanh::lean_apply_2(
                            v_matchLocalDecl_x3f_6469_,
                            v_val_6477_,
                            v_givenName_6470_,
                        );
                        return v___x_6479_;
                    } else {
                        if v_skipAuxDecl_6471_ == 0 {
                            if v___x_6478_ == 0 {
                                leanh::lean_dec_ref_known(v_x_6476_, 1);
                                leanh::lean_dec_ref(v_givenNameView_6475_);
                                leanh::lean_dec(v_currNamespace_6474_);
                                leanh::lean_dec(v_auxDeclToFullName_6473_);
                                leanh::lean_dec_ref(v___f_6472_);
                                leanh::lean_dec(v_givenName_6470_);
                                leanh::lean_dec_ref(v_matchLocalDecl_x3f_6469_);
                                v___x_6480_ = leanh::lean_box(0);
                                return v___x_6480_;
                            } else {
                                v___x_6481_ = l_Lean_LocalDecl_fvarId(v_val_6477_);
                                v___x_6482_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(
                                    v___f_6472_,
                                    v_auxDeclToFullName_6473_,
                                    v___x_6481_,
                                );
                                if leanh::lean_obj_tag(v___x_6482_) == 1 {
                                    leanh::lean_dec(v_givenName_6470_);
                                    leanh::lean_dec_ref(v_matchLocalDecl_x3f_6469_);
                                    v_val_6483_ = leanh::lean_ctor_get(v___x_6482_, 0);
                                    leanh::lean_inc(v_val_6483_);
                                    leanh::lean_dec_ref_known(v___x_6482_, 1);
                                    v_fullDeclView_6484_ = l_Lean_extractMacroScopes(v_val_6483_);
                                    v_name_6507_ =
                                        leanh::lean_ctor_get(v_fullDeclView_6484_, 0);
                                    leanh::lean_inc_n(v_name_6507_, 2);
                                    v___x_6508_ = lean_private_to_user_name(v_name_6507_);
                                    if leanh::lean_obj_tag(v___x_6508_) == 0 {
                                        v___y_6486_ = v_name_6507_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_name_6507_);
                                        v_val_6509_ = leanh::lean_ctor_get(v___x_6508_, 0);
                                        leanh::lean_inc(v_val_6509_);
                                        leanh::lean_dec_ref_known(v___x_6508_, 1);
                                        v___y_6486_ = v_val_6509_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_inc(v_val_6477_);
                                    leanh::lean_dec(v___x_6482_);
                                    leanh::lean_dec_ref_known(v_x_6476_, 1);
                                    leanh::lean_dec_ref(v_givenNameView_6475_);
                                    leanh::lean_dec(v_currNamespace_6474_);
                                    v___x_6510_ = leanh::lean_apply_2(
                                        v_matchLocalDecl_x3f_6469_,
                                        v_val_6477_,
                                        v_givenName_6470_,
                                    );
                                    return v___x_6510_;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_x_6476_, 1);
                            leanh::lean_dec_ref(v_givenNameView_6475_);
                            leanh::lean_dec(v_currNamespace_6474_);
                            leanh::lean_dec(v_auxDeclToFullName_6473_);
                            leanh::lean_dec_ref(v___f_6472_);
                            leanh::lean_dec(v_givenName_6470_);
                            leanh::lean_dec_ref(v_matchLocalDecl_x3f_6469_);
                            v___x_6511_ = leanh::lean_box(0);
                            return v___x_6511_;
                        }
                    }
                }
            }
            1 => {
                v_imported_6487_ = leanh::lean_ctor_get(v_fullDeclView_6484_, 1);
                v_ctx_6488_ = leanh::lean_ctor_get(v_fullDeclView_6484_, 2);
                v_scopes_6489_ = leanh::lean_ctor_get(v_fullDeclView_6484_, 3);
                v_isSharedCheck_6505_ =
                    (!leanh::lean_is_exclusive(v_fullDeclView_6484_)) as u8;
                if v_isSharedCheck_6505_ == 0 {
                    v_unused_6506_ = leanh::lean_ctor_get(v_fullDeclView_6484_, 0);
                    leanh::lean_dec(v_unused_6506_);
                    v___x_6491_ = v_fullDeclView_6484_;
                    v_isShared_6492_ = v_isSharedCheck_6505_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_scopes_6489_);
                    leanh::lean_inc(v_ctx_6488_);
                    leanh::lean_inc(v_imported_6487_);
                    leanh::lean_dec(v_fullDeclView_6484_);
                    v___x_6491_ = leanh::lean_box(0);
                    v_isShared_6492_ = v_isSharedCheck_6505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_6492_ == 0 {
                    leanh::lean_ctor_set(v___x_6491_, 0, v___y_6486_);
                    v_fullDeclView_6494_ = v___x_6491_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6504_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6504_, 0, v___y_6486_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6504_, 1, v_imported_6487_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6504_, 2, v_ctx_6488_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6504_, 3, v_scopes_6489_);
                    v_fullDeclView_6494_ = v_reuseFailAlloc_6504_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v_fullDeclView_6494_);
                v_fullDeclName_6495_ = l_Lean_MacroScopesView_review(v_fullDeclView_6494_);
                v___x_6496_ = l_Lean_Name_isPrefixOf(v_currNamespace_6474_, v_fullDeclName_6495_);
                if v___x_6496_ == 0 {
                    leanh::lean_inc(v_val_6477_);
                    leanh::lean_dec_ref(v_fullDeclView_6494_);
                    leanh::lean_dec_ref_known(v_x_6476_, 1);
                    v___x_6497_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(
                        v_val_6477_,
                        v_givenNameView_6475_,
                        v_fullDeclName_6495_,
                        v_currNamespace_6474_,
                    );
                    leanh::lean_dec(v_fullDeclName_6495_);
                    return v___x_6497_;
                } else {
                    leanh::lean_dec(v_fullDeclName_6495_);
                    leanh::lean_dec(v_currNamespace_6474_);
                    v___x_6498_ = l_Lean_LocalDecl_userName(v_val_6477_);
                    v_localDeclNameView_6499_ = l_Lean_extractMacroScopes(v___x_6498_);
                    v___x_6500_ = l_Lean_MacroScopesView_isSuffixOf(
                        v_localDeclNameView_6499_,
                        v_givenNameView_6475_,
                    );
                    leanh::lean_dec_ref(v_localDeclNameView_6499_);
                    if v___x_6500_ == 0 {
                        leanh::lean_dec_ref(v_fullDeclView_6494_);
                        leanh::lean_dec_ref_known(v_x_6476_, 1);
                        leanh::lean_dec_ref(v_givenNameView_6475_);
                        v___x_6501_ = leanh::lean_box(0);
                        return v___x_6501_;
                    } else {
                        v___x_6502_ = l_Lean_MacroScopesView_isSuffixOf(
                            v_givenNameView_6475_,
                            v_fullDeclView_6494_,
                        );
                        leanh::lean_dec_ref(v_fullDeclView_6494_);
                        leanh::lean_dec_ref(v_givenNameView_6475_);
                        if v___x_6502_ == 0 {
                            leanh::lean_dec_ref_known(v_x_6476_, 1);
                            v___x_6503_ = leanh::lean_box(0);
                            return v___x_6503_;
                        } else {
                            return v_x_6476_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_resolveLocalName___redArg___lam__1___boxed(
    mut v_matchLocalDecl_x3f_6512_: *mut leanh::LeanObject,
    mut v_givenName_6513_: *mut leanh::LeanObject,
    mut v_skipAuxDecl_6514_: *mut leanh::LeanObject,
    mut v___f_6515_: *mut leanh::LeanObject,
    mut v_auxDeclToFullName_6516_: *mut leanh::LeanObject,
    mut v_currNamespace_6517_: *mut leanh::LeanObject,
    mut v_givenNameView_6518_: *mut leanh::LeanObject,
    mut v_x_6519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipAuxDecl_boxed_6520_: u8 = 0;
    let mut v_res_6521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipAuxDecl_boxed_6520_ = (leanh::lean_unbox(v_skipAuxDecl_6514_) as u8);
    v_res_6521_ = l_Lean_resolveLocalName___redArg___lam__1(
        v_matchLocalDecl_x3f_6512_,
        v_givenName_6513_,
        v_skipAuxDecl_boxed_6520_,
        v___f_6515_,
        v_auxDeclToFullName_6516_,
        v_currNamespace_6517_,
        v_givenNameView_6518_,
        v_x_6519_,
    );
    return v_res_6521_;
}
pub unsafe fn l_Lean_resolveLocalName___redArg___lam__2(
    mut v_localDecl_x3f_6522_: *mut leanh::LeanObject,
    mut v_matchLocalDecl_x3f_6523_: *mut leanh::LeanObject,
    mut v_givenName_6524_: *mut leanh::LeanObject,
    mut v_x_6525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6525_) == 0 {
        leanh::lean_dec(v_givenName_6524_);
        leanh::lean_dec_ref(v_matchLocalDecl_x3f_6523_);
        return v_x_6525_;
    } else {
        let mut v_val_6526_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6527_: u8 = 0;
        v_val_6526_ = leanh::lean_ctor_get(v_x_6525_, 0);
        leanh::lean_inc(v_val_6526_);
        leanh::lean_dec_ref_known(v_x_6525_, 1);
        v___x_6527_ = l_Lean_LocalDecl_isAuxDecl(v_val_6526_);
        if v___x_6527_ == 0 {
            leanh::lean_dec(v_val_6526_);
            leanh::lean_dec(v_givenName_6524_);
            leanh::lean_dec_ref(v_matchLocalDecl_x3f_6523_);
            leanh::lean_inc(v_localDecl_x3f_6522_);
            return v_localDecl_x3f_6522_;
        } else {
            let mut v___x_6528_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_6528_ = leanh::lean_apply_2(
                v_matchLocalDecl_x3f_6523_,
                v_val_6526_,
                v_givenName_6524_,
            );
            return v___x_6528_;
        }
    }
}
pub unsafe fn l_Lean_resolveLocalName___redArg___lam__2___boxed(
    mut v_localDecl_x3f_6529_: *mut leanh::LeanObject,
    mut v_matchLocalDecl_x3f_6530_: *mut leanh::LeanObject,
    mut v_givenName_6531_: *mut leanh::LeanObject,
    mut v_x_6532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6533_ = l_Lean_resolveLocalName___redArg___lam__2(
        v_localDecl_x3f_6529_,
        v_matchLocalDecl_x3f_6530_,
        v_givenName_6531_,
        v_x_6532_,
    );
    leanh::lean_dec(v_localDecl_x3f_6529_);
    return v_res_6533_;
}
pub unsafe fn l_Lean_resolveLocalName___redArg___lam__3(
    mut v_lctx_6553_: *mut leanh::LeanObject,
    mut v_matchLocalDecl_x3f_6554_: *mut leanh::LeanObject,
    mut v___f_6555_: *mut leanh::LeanObject,
    mut v_auxDeclToFullName_6556_: *mut leanh::LeanObject,
    mut v_currNamespace_6557_: *mut leanh::LeanObject,
    mut v_givenNameView_6558_: *mut leanh::LeanObject,
    mut v_skipAuxDecl_6559_: u8,
) -> *mut leanh::LeanObject {
    let mut v_decls_6560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_givenName_6561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localDecl_x3f_6565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_decls_6560_ = leanh::lean_ctor_get(v_lctx_6553_, 1);
    leanh::lean_inc_ref_n(v_decls_6560_, 2);
    leanh::lean_dec_ref(v_lctx_6553_);
    leanh::lean_inc_ref(v_givenNameView_6558_);
    v_givenName_6561_ = l_Lean_MacroScopesView_review(v_givenNameView_6558_);
    v___x_6562_ = leanh::lean_box((v_skipAuxDecl_6559_) as usize);
    leanh::lean_inc(v_givenName_6561_);
    leanh::lean_inc_ref(v_matchLocalDecl_x3f_6554_);
    v___f_6563_ = leanh::lean_alloc_closure(
        l_Lean_resolveLocalName___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_6563_, 0, v_matchLocalDecl_x3f_6554_);
    leanh::lean_closure_set(v___f_6563_, 1, v_givenName_6561_);
    leanh::lean_closure_set(v___f_6563_, 2, v___x_6562_);
    leanh::lean_closure_set(v___f_6563_, 3, v___f_6555_);
    leanh::lean_closure_set(v___f_6563_, 4, v_auxDeclToFullName_6556_);
    leanh::lean_closure_set(v___f_6563_, 5, v_currNamespace_6557_);
    leanh::lean_closure_set(v___f_6563_, 6, v_givenNameView_6558_);
    v___x_6564_ = l_Lean_resolveLocalName___redArg___lam__3___closed__9;
    v_localDecl_x3f_6565_ =
        l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_6564_, v_decls_6560_, v___f_6563_);
    if leanh::lean_obj_tag(v_localDecl_x3f_6565_) == 0 {
        if v_skipAuxDecl_6559_ == 0 {
            let mut v___f_6566_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6567_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___f_6566_ = leanh::lean_alloc_closure(
                l_Lean_resolveLocalName___redArg___lam__2___boxed as *mut core::ffi::c_void,
                4,
                3,
            );
            leanh::lean_closure_set(v___f_6566_, 0, v_localDecl_x3f_6565_);
            leanh::lean_closure_set(v___f_6566_, 1, v_matchLocalDecl_x3f_6554_);
            leanh::lean_closure_set(v___f_6566_, 2, v_givenName_6561_);
            v___x_6567_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(
                v___x_6564_,
                v_decls_6560_,
                v___f_6566_,
            );
            return v___x_6567_;
        } else {
            leanh::lean_dec(v_givenName_6561_);
            leanh::lean_dec_ref(v_decls_6560_);
            leanh::lean_dec_ref(v_matchLocalDecl_x3f_6554_);
            return v_localDecl_x3f_6565_;
        }
    } else {
        leanh::lean_dec(v_givenName_6561_);
        leanh::lean_dec_ref(v_decls_6560_);
        leanh::lean_dec_ref(v_matchLocalDecl_x3f_6554_);
        return v_localDecl_x3f_6565_;
    }
}
pub unsafe fn l_Lean_resolveLocalName___redArg___lam__3___boxed(
    mut v_lctx_6568_: *mut leanh::LeanObject,
    mut v_matchLocalDecl_x3f_6569_: *mut leanh::LeanObject,
    mut v___f_6570_: *mut leanh::LeanObject,
    mut v_auxDeclToFullName_6571_: *mut leanh::LeanObject,
    mut v_currNamespace_6572_: *mut leanh::LeanObject,
    mut v_givenNameView_6573_: *mut leanh::LeanObject,
    mut v_skipAuxDecl_6574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipAuxDecl_boxed_6575_: u8 = 0;
    let mut v_res_6576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipAuxDecl_boxed_6575_ = (leanh::lean_unbox(v_skipAuxDecl_6574_) as u8);
    v_res_6576_ = l_Lean_resolveLocalName___redArg___lam__3(
        v_lctx_6568_,
        v_matchLocalDecl_x3f_6569_,
        v___f_6570_,
        v_auxDeclToFullName_6571_,
        v_currNamespace_6572_,
        v_givenNameView_6573_,
        v_skipAuxDecl_boxed_6575_,
    );
    return v_res_6576_;
}
pub unsafe fn l_Lean_resolveLocalName___redArg___lam__4(
    mut v_n_6577_: *mut leanh::LeanObject,
    mut v_lctx_6578_: *mut leanh::LeanObject,
    mut v_matchLocalDecl_x3f_6579_: *mut leanh::LeanObject,
    mut v___f_6580_: *mut leanh::LeanObject,
    mut v_auxDeclToFullName_6581_: *mut leanh::LeanObject,
    mut v_inst_6582_: *mut leanh::LeanObject,
    mut v_inst_6583_: *mut leanh::LeanObject,
    mut v_inst_6584_: *mut leanh::LeanObject,
    mut v_inst_6585_: *mut leanh::LeanObject,
    mut v_inst_6586_: *mut leanh::LeanObject,
    mut v_inst_6587_: *mut leanh::LeanObject,
    mut v_currNamespace_6588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_view_6589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_6590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_findLocalDecl_x3f_6591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: u8 = 0;
    let mut v___x_6594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_view_6589_ = l_Lean_extractMacroScopes(v_n_6577_);
    v_name_6590_ = leanh::lean_ctor_get(v_view_6589_, 0);
    leanh::lean_inc(v_name_6590_);
    v_findLocalDecl_x3f_6591_ = leanh::lean_alloc_closure(
        l_Lean_resolveLocalName___redArg___lam__3___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    leanh::lean_closure_set(v_findLocalDecl_x3f_6591_, 0, v_lctx_6578_);
    leanh::lean_closure_set(v_findLocalDecl_x3f_6591_, 1, v_matchLocalDecl_x3f_6579_);
    leanh::lean_closure_set(v_findLocalDecl_x3f_6591_, 2, v___f_6580_);
    leanh::lean_closure_set(v_findLocalDecl_x3f_6591_, 3, v_auxDeclToFullName_6581_);
    leanh::lean_closure_set(v_findLocalDecl_x3f_6591_, 4, v_currNamespace_6588_);
    v___x_6592_ = leanh::lean_box(0);
    v___x_6593_ = 0;
    v___x_6594_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(
        v_inst_6582_,
        v_inst_6583_,
        v_inst_6584_,
        v_inst_6585_,
        v_inst_6586_,
        v_inst_6587_,
        v_view_6589_,
        v_findLocalDecl_x3f_6591_,
        v_name_6590_,
        v___x_6592_,
        v___x_6593_,
    );
    return v___x_6594_;
}
pub unsafe fn l_Lean_resolveLocalName___redArg___lam__5(
    mut v_inst_6595_: *mut leanh::LeanObject,
    mut v_n_6596_: *mut leanh::LeanObject,
    mut v_lctx_6597_: *mut leanh::LeanObject,
    mut v_matchLocalDecl_x3f_6598_: *mut leanh::LeanObject,
    mut v___f_6599_: *mut leanh::LeanObject,
    mut v_inst_6600_: *mut leanh::LeanObject,
    mut v_inst_6601_: *mut leanh::LeanObject,
    mut v_inst_6602_: *mut leanh::LeanObject,
    mut v_inst_6603_: *mut leanh::LeanObject,
    mut v_inst_6604_: *mut leanh::LeanObject,
    mut v_toBind_6605_: *mut leanh::LeanObject,
    mut v_____do__lift_6606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_auxDeclToFullName_6607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getCurrNamespace_6608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_auxDeclToFullName_6607_ = leanh::lean_ctor_get(v_____do__lift_6606_, 2);
    leanh::lean_inc(v_auxDeclToFullName_6607_);
    leanh::lean_dec_ref(v_____do__lift_6606_);
    v_getCurrNamespace_6608_ = leanh::lean_ctor_get(v_inst_6595_, 0);
    leanh::lean_inc(v_getCurrNamespace_6608_);
    v___f_6609_ = leanh::lean_alloc_closure(
        l_Lean_resolveLocalName___redArg___lam__4 as *mut core::ffi::c_void,
        12,
        11,
    );
    leanh::lean_closure_set(v___f_6609_, 0, v_n_6596_);
    leanh::lean_closure_set(v___f_6609_, 1, v_lctx_6597_);
    leanh::lean_closure_set(v___f_6609_, 2, v_matchLocalDecl_x3f_6598_);
    leanh::lean_closure_set(v___f_6609_, 3, v___f_6599_);
    leanh::lean_closure_set(v___f_6609_, 4, v_auxDeclToFullName_6607_);
    leanh::lean_closure_set(v___f_6609_, 5, v_inst_6600_);
    leanh::lean_closure_set(v___f_6609_, 6, v_inst_6595_);
    leanh::lean_closure_set(v___f_6609_, 7, v_inst_6601_);
    leanh::lean_closure_set(v___f_6609_, 8, v_inst_6602_);
    leanh::lean_closure_set(v___f_6609_, 9, v_inst_6603_);
    leanh::lean_closure_set(v___f_6609_, 10, v_inst_6604_);
    v___x_6610_ = leanh::lean_apply_4(
        v_toBind_6605_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getCurrNamespace_6608_,
        v___f_6609_,
    );
    return v___x_6610_;
}
pub unsafe fn l_Lean_resolveLocalName___redArg___lam__6(
    mut v_inst_6611_: *mut leanh::LeanObject,
    mut v_n_6612_: *mut leanh::LeanObject,
    mut v_matchLocalDecl_x3f_6613_: *mut leanh::LeanObject,
    mut v___f_6614_: *mut leanh::LeanObject,
    mut v_inst_6615_: *mut leanh::LeanObject,
    mut v_inst_6616_: *mut leanh::LeanObject,
    mut v_inst_6617_: *mut leanh::LeanObject,
    mut v_inst_6618_: *mut leanh::LeanObject,
    mut v_inst_6619_: *mut leanh::LeanObject,
    mut v_toBind_6620_: *mut leanh::LeanObject,
    mut v_inst_6621_: *mut leanh::LeanObject,
    mut v_lctx_6622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6624_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_6620_);
    v___f_6623_ = leanh::lean_alloc_closure(
        l_Lean_resolveLocalName___redArg___lam__5 as *mut core::ffi::c_void,
        12,
        11,
    );
    leanh::lean_closure_set(v___f_6623_, 0, v_inst_6611_);
    leanh::lean_closure_set(v___f_6623_, 1, v_n_6612_);
    leanh::lean_closure_set(v___f_6623_, 2, v_lctx_6622_);
    leanh::lean_closure_set(v___f_6623_, 3, v_matchLocalDecl_x3f_6613_);
    leanh::lean_closure_set(v___f_6623_, 4, v___f_6614_);
    leanh::lean_closure_set(v___f_6623_, 5, v_inst_6615_);
    leanh::lean_closure_set(v___f_6623_, 6, v_inst_6616_);
    leanh::lean_closure_set(v___f_6623_, 7, v_inst_6617_);
    leanh::lean_closure_set(v___f_6623_, 8, v_inst_6618_);
    leanh::lean_closure_set(v___f_6623_, 9, v_inst_6619_);
    leanh::lean_closure_set(v___f_6623_, 10, v_toBind_6620_);
    v___x_6624_ = leanh::lean_apply_4(
        v_toBind_6620_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_6621_,
        v___f_6623_,
    );
    return v___x_6624_;
}
pub unsafe fn l_Lean_resolveLocalName___redArg(
    mut v_inst_6627_: *mut leanh::LeanObject,
    mut v_inst_6628_: *mut leanh::LeanObject,
    mut v_inst_6629_: *mut leanh::LeanObject,
    mut v_inst_6630_: *mut leanh::LeanObject,
    mut v_inst_6631_: *mut leanh::LeanObject,
    mut v_inst_6632_: *mut leanh::LeanObject,
    mut v_inst_6633_: *mut leanh::LeanObject,
    mut v_n_6634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_6635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_matchLocalDecl_x3f_6637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_6635_ = leanh::lean_ctor_get(v_inst_6627_, 1);
    leanh::lean_inc_n(v_toBind_6635_, 2);
    v___f_6636_ = l_Lean_resolveLocalName___redArg___closed__0;
    v_matchLocalDecl_x3f_6637_ = l_Lean_resolveLocalName___redArg___closed__1;
    leanh::lean_inc(v_inst_6633_);
    v___f_6638_ = leanh::lean_alloc_closure(
        l_Lean_resolveLocalName___redArg___lam__6 as *mut core::ffi::c_void,
        12,
        11,
    );
    leanh::lean_closure_set(v___f_6638_, 0, v_inst_6628_);
    leanh::lean_closure_set(v___f_6638_, 1, v_n_6634_);
    leanh::lean_closure_set(v___f_6638_, 2, v_matchLocalDecl_x3f_6637_);
    leanh::lean_closure_set(v___f_6638_, 3, v___f_6636_);
    leanh::lean_closure_set(v___f_6638_, 4, v_inst_6627_);
    leanh::lean_closure_set(v___f_6638_, 5, v_inst_6629_);
    leanh::lean_closure_set(v___f_6638_, 6, v_inst_6630_);
    leanh::lean_closure_set(v___f_6638_, 7, v_inst_6631_);
    leanh::lean_closure_set(v___f_6638_, 8, v_inst_6632_);
    leanh::lean_closure_set(v___f_6638_, 9, v_toBind_6635_);
    leanh::lean_closure_set(v___f_6638_, 10, v_inst_6633_);
    v___x_6639_ = leanh::lean_apply_4(
        v_toBind_6635_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_6633_,
        v___f_6638_,
    );
    return v___x_6639_;
}
pub unsafe fn l_Lean_resolveLocalName(
    mut v_m_6640_: *mut leanh::LeanObject,
    mut v_inst_6641_: *mut leanh::LeanObject,
    mut v_inst_6642_: *mut leanh::LeanObject,
    mut v_inst_6643_: *mut leanh::LeanObject,
    mut v_inst_6644_: *mut leanh::LeanObject,
    mut v_inst_6645_: *mut leanh::LeanObject,
    mut v_inst_6646_: *mut leanh::LeanObject,
    mut v_inst_6647_: *mut leanh::LeanObject,
    mut v_n_6648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6649_ = l_Lean_resolveLocalName___redArg(
        v_inst_6641_,
        v_inst_6642_,
        v_inst_6643_,
        v_inst_6644_,
        v_inst_6645_,
        v_inst_6646_,
        v_inst_6647_,
        v_n_6648_,
    );
    return v___x_6649_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(
    mut v_toPure_6650_: *mut leanh::LeanObject,
    mut v_____do__lift_6651_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_6652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6652_ = leanh::lean_box((v_____do__lift_6651_) as usize);
    v___x_6653_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6653_, 0, v___x_6652_);
    v___x_6654_ =
        leanh::lean_apply_2(v_toPure_6650_, leanh::lean_box(0), v___x_6653_);
    return v___x_6654_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed(
    mut v_toPure_6655_: *mut leanh::LeanObject,
    mut v_____do__lift_6656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_1160__boxed_6657_: u8 = 0;
    let mut v_res_6658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_1160__boxed_6657_ = (leanh::lean_unbox(v_____do__lift_6656_) as u8);
    v_res_6658_ =
        l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(
            v_toPure_6655_,
            v_____do__lift_1160__boxed_6657_,
        );
    return v_res_6658_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1(
    mut v_toPure_6659_: *mut leanh::LeanObject,
    mut v___y_6660_: *mut leanh::LeanObject,
    mut v_____do__lift_6661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6666_: u8 = 0;
    let mut v___x_6668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6671_: u8 = 0;
    let mut v_unused_6672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_6661_) == 0 {
                    leanh::lean_dec(v___y_6660_);
                    v___x_6662_ = leanh::lean_box(0);
                    v___x_6663_ = leanh::lean_apply_2(
                        v_toPure_6659_,
                        leanh::lean_box(0),
                        v___x_6662_,
                    );
                    return v___x_6663_;
                } else {
                    v_isSharedCheck_6671_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_6661_)) as u8;
                    if v_isSharedCheck_6671_ == 0 {
                        v_unused_6672_ = leanh::lean_ctor_get(v_____do__lift_6661_, 0);
                        leanh::lean_dec(v_unused_6672_);
                        v___x_6665_ = v_____do__lift_6661_;
                        v_isShared_6666_ = v_isSharedCheck_6671_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_____do__lift_6661_);
                        v___x_6665_ = leanh::lean_box(0);
                        v_isShared_6666_ = v_isSharedCheck_6671_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6666_ == 0 {
                    leanh::lean_ctor_set(v___x_6665_, 0, v___y_6660_);
                    v___x_6668_ = v___x_6665_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6670_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6670_, 0, v___y_6660_);
                    v___x_6668_ = v_reuseFailAlloc_6670_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6669_ = leanh::lean_apply_2(
                    v_toPure_6659_,
                    leanh::lean_box(0),
                    v___x_6668_,
                );
                return v___x_6669_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(
    mut v_toPure_6675_: *mut leanh::LeanObject,
    mut v_toBind_6676_: *mut leanh::LeanObject,
    mut v___f_6677_: *mut leanh::LeanObject,
    mut v_____do__lift_6678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_6678_) == 0 {
        let mut v___x_6679_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6680_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_6677_);
        leanh::lean_dec(v_toBind_6676_);
        v___x_6679_ = leanh::lean_box(0);
        v___x_6680_ =
            leanh::lean_apply_2(v_toPure_6675_, leanh::lean_box(0), v___x_6679_);
        return v___x_6680_;
    } else {
        let mut v_val_6681_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6682_: u8 = 0;
        v_val_6681_ = leanh::lean_ctor_get(v_____do__lift_6678_, 0);
        v___x_6682_ = (leanh::lean_unbox(v_val_6681_) as u8);
        if v___x_6682_ == 0 {
            let mut v___x_6683_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6684_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6685_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_6683_ = leanh::lean_box(0);
            v___x_6684_ =
                leanh::lean_apply_2(v_toPure_6675_, leanh::lean_box(0), v___x_6683_);
            v___x_6685_ = leanh::lean_apply_4(
                v_toBind_6676_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_6684_,
                v___f_6677_,
            );
            return v___x_6685_;
        } else {
            let mut v___x_6686_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6687_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6688_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_6686_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0;
            v___x_6687_ =
                leanh::lean_apply_2(v_toPure_6675_, leanh::lean_box(0), v___x_6686_);
            v___x_6688_ = leanh::lean_apply_4(
                v_toBind_6676_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_6687_,
                v___f_6677_,
            );
            return v___x_6688_;
        }
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed(
    mut v_toPure_6689_: *mut leanh::LeanObject,
    mut v_toBind_6690_: *mut leanh::LeanObject,
    mut v___f_6691_: *mut leanh::LeanObject,
    mut v_____do__lift_6692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6693_ =
        l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(
            v_toPure_6689_,
            v_toBind_6690_,
            v___f_6691_,
            v_____do__lift_6692_,
        );
    leanh::lean_dec(v_____do__lift_6692_);
    return v_res_6693_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(
    mut v_toPure_6694_: *mut leanh::LeanObject,
    mut v_filter_6695_: *mut leanh::LeanObject,
    mut v___y_6696_: *mut leanh::LeanObject,
    mut v_toBind_6697_: *mut leanh::LeanObject,
    mut v___f_6698_: *mut leanh::LeanObject,
    mut v___f_6699_: *mut leanh::LeanObject,
    mut v_____do__lift_6700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_6700_) == 0 {
        let mut v___x_6701_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6702_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_6699_);
        leanh::lean_dec(v___f_6698_);
        leanh::lean_dec(v_toBind_6697_);
        leanh::lean_dec(v___y_6696_);
        leanh::lean_dec(v_filter_6695_);
        v___x_6701_ = leanh::lean_box(0);
        v___x_6702_ =
            leanh::lean_apply_2(v_toPure_6694_, leanh::lean_box(0), v___x_6701_);
        return v___x_6702_;
    } else {
        let mut v___x_6703_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6704_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6705_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_6694_);
        v___x_6703_ = leanh::lean_apply_1(v_filter_6695_, v___y_6696_);
        leanh::lean_inc(v_toBind_6697_);
        v___x_6704_ = leanh::lean_apply_4(
            v_toBind_6697_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_6703_,
            v___f_6698_,
        );
        v___x_6705_ = leanh::lean_apply_4(
            v_toBind_6697_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_6704_,
            v___f_6699_,
        );
        return v___x_6705_;
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed(
    mut v_toPure_6706_: *mut leanh::LeanObject,
    mut v_filter_6707_: *mut leanh::LeanObject,
    mut v___y_6708_: *mut leanh::LeanObject,
    mut v_toBind_6709_: *mut leanh::LeanObject,
    mut v___f_6710_: *mut leanh::LeanObject,
    mut v___f_6711_: *mut leanh::LeanObject,
    mut v_____do__lift_6712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6713_ =
        l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(
            v_toPure_6706_,
            v_filter_6707_,
            v___y_6708_,
            v_toBind_6709_,
            v___f_6710_,
            v___f_6711_,
            v_____do__lift_6712_,
        );
    leanh::lean_dec(v_____do__lift_6712_);
    return v_res_6713_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(
    mut v_toPure_6714_: *mut leanh::LeanObject,
    mut v_n_u2080_6715_: *mut leanh::LeanObject,
    mut v_toBind_6716_: *mut leanh::LeanObject,
    mut v___f_6717_: *mut leanh::LeanObject,
    mut v_____do__lift_6718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6728_: u8 = 0;
    let mut v___x_6729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_6718_) == 0 {
                    leanh::lean_dec(v___f_6717_);
                    leanh::lean_dec(v_toBind_6716_);
                    v___x_6722_ = leanh::lean_box(0);
                    v___x_6723_ = leanh::lean_apply_2(
                        v_toPure_6714_,
                        leanh::lean_box(0),
                        v___x_6722_,
                    );
                    return v___x_6723_;
                } else {
                    v_val_6724_ = leanh::lean_ctor_get(v_____do__lift_6718_, 0);
                    if leanh::lean_obj_tag(v_val_6724_) == 1 {
                        v_tail_6725_ = leanh::lean_ctor_get(v_val_6724_, 1);
                        if leanh::lean_obj_tag(v_tail_6725_) == 0 {
                            v_head_6726_ = leanh::lean_ctor_get(v_val_6724_, 0);
                            v_fst_6727_ = leanh::lean_ctor_get(v_head_6726_, 0);
                            v___x_6728_ = lean_name_eq(v_fst_6727_, v_n_u2080_6715_);
                            if v___x_6728_ == 0 {
                                v___x_6729_ = leanh::lean_box(0);
                                v___x_6730_ = leanh::lean_apply_2(
                                    v_toPure_6714_,
                                    leanh::lean_box(0),
                                    v___x_6729_,
                                );
                                v___x_6731_ = leanh::lean_apply_4(
                                    v_toBind_6716_,
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_6730_,
                                    v___f_6717_,
                                );
                                return v___x_6731_;
                            } else {
                                v___x_6732_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0;
                                v___x_6733_ = leanh::lean_apply_2(
                                    v_toPure_6714_,
                                    leanh::lean_box(0),
                                    v___x_6732_,
                                );
                                v___x_6734_ = leanh::lean_apply_4(
                                    v_toBind_6716_,
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_6733_,
                                    v___f_6717_,
                                );
                                return v___x_6734_;
                            }
                        } else {
                            leanh::lean_dec(v___f_6717_);
                            leanh::lean_dec(v_toBind_6716_);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___f_6717_);
                        leanh::lean_dec(v_toBind_6716_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6720_ = leanh::lean_box(0);
                v___x_6721_ = leanh::lean_apply_2(
                    v_toPure_6714_,
                    leanh::lean_box(0),
                    v___x_6720_,
                );
                return v___x_6721_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed(
    mut v_toPure_6735_: *mut leanh::LeanObject,
    mut v_n_u2080_6736_: *mut leanh::LeanObject,
    mut v_toBind_6737_: *mut leanh::LeanObject,
    mut v___f_6738_: *mut leanh::LeanObject,
    mut v_____do__lift_6739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6740_ =
        l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(
            v_toPure_6735_,
            v_n_u2080_6736_,
            v_toBind_6737_,
            v___f_6738_,
            v_____do__lift_6739_,
        );
    leanh::lean_dec(v_____do__lift_6739_);
    leanh::lean_dec(v_n_u2080_6736_);
    return v_res_6740_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(
    mut v_inst_6741_: *mut leanh::LeanObject,
    mut v_inst_6742_: *mut leanh::LeanObject,
    mut v_inst_6743_: *mut leanh::LeanObject,
    mut v_inst_6744_: *mut leanh::LeanObject,
    mut v_inst_6745_: *mut leanh::LeanObject,
    mut v_inst_6746_: *mut leanh::LeanObject,
    mut v_n_u2080_6747_: *mut leanh::LeanObject,
    mut v_filter_6748_: *mut leanh::LeanObject,
    mut v_view_x3f_6749_: *mut leanh::LeanObject,
    mut v_n_6750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_6764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_6765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6768_: u8 = 0;
    let mut v_toBind_6769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: u8 = 0;
    let mut v___x_6787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_imported_6790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_6791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6795_: u8 = 0;
    let mut v___x_6797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6800_: u8 = 0;
    let mut v_unused_6801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6803_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref_n(v_inst_6741_, 8);
                v___f_6751_ = leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                leanh::lean_closure_set(v___f_6751_, 0, v_inst_6741_);
                v___f_6752_ = leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                leanh::lean_closure_set(v___f_6752_, 0, v_inst_6741_);
                v___f_6753_ = leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__6 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                leanh::lean_closure_set(v___f_6753_, 0, v_inst_6741_);
                v___f_6754_ = leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                leanh::lean_closure_set(v___f_6754_, 0, v_inst_6741_);
                v___f_6755_ = leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__11 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                leanh::lean_closure_set(v___f_6755_, 0, v_inst_6741_);
                v___x_6756_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6756_, 0, v___f_6751_);
                leanh::lean_ctor_set(v___x_6756_, 1, v___f_6752_);
                v___x_6757_ = leanh::lean_alloc_closure(
                    l_OptionT_pure as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___x_6757_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_6757_, 1, v_inst_6741_);
                v___x_6758_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_6758_, 0, v___x_6756_);
                leanh::lean_ctor_set(v___x_6758_, 1, v___x_6757_);
                leanh::lean_ctor_set(v___x_6758_, 2, v___f_6753_);
                leanh::lean_ctor_set(v___x_6758_, 3, v___f_6754_);
                leanh::lean_ctor_set(v___x_6758_, 4, v___f_6755_);
                v___x_6759_ = leanh::lean_alloc_closure(
                    l_OptionT_bind as *mut core::ffi::c_void,
                    6,
                    2,
                );
                leanh::lean_closure_set(v___x_6759_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_6759_, 1, v_inst_6741_);
                v___x_6760_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6760_, 0, v___x_6758_);
                leanh::lean_ctor_set(v___x_6760_, 1, v___x_6759_);
                v___x_6761_ = leanh::lean_alloc_closure(
                    l_OptionT_lift as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___x_6761_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_6761_, 1, v_inst_6741_);
                leanh::lean_inc_ref(v___x_6761_);
                v___x_6762_ =
                    l_Lean_instMonadResolveNameOfMonadLift___redArg(v___x_6761_, v_inst_6742_);
                v_toApplicative_6763_ = leanh::lean_ctor_get(v_inst_6741_, 0);
                leanh::lean_inc_ref(v_toApplicative_6763_);
                v_getEnv_6764_ = leanh::lean_ctor_get(v_inst_6743_, 0);
                v_modifyEnv_6765_ = leanh::lean_ctor_get(v_inst_6743_, 1);
                v_isSharedCheck_6803_ = (!leanh::lean_is_exclusive(v_inst_6743_)) as u8;
                if v_isSharedCheck_6803_ == 0 {
                    v___x_6767_ = v_inst_6743_;
                    v_isShared_6768_ = v_isSharedCheck_6803_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyEnv_6765_);
                    leanh::lean_inc(v_getEnv_6764_);
                    leanh::lean_dec(v_inst_6743_);
                    v___x_6767_ = leanh::lean_box(0);
                    v_isShared_6768_ = v_isSharedCheck_6803_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toBind_6769_ = leanh::lean_ctor_get(v_inst_6741_, 1);
                leanh::lean_inc_n(v_toBind_6769_, 2);
                leanh::lean_dec_ref(v_inst_6741_);
                v_toPure_6770_ = leanh::lean_ctor_get(v_toApplicative_6763_, 1);
                leanh::lean_inc_n(v_toPure_6770_, 3);
                leanh::lean_dec_ref(v_toApplicative_6763_);
                leanh::lean_inc_ref(v___x_6761_);
                v___f_6771_ = leanh::lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_6771_, 0, v_modifyEnv_6765_);
                leanh::lean_closure_set(v___f_6771_, 1, v___x_6761_);
                v___f_6772_ = leanh::lean_alloc_closure(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_6772_, 0, v_toPure_6770_);
                v___f_6773_ = leanh::lean_alloc_closure(
                    l_OptionT_lift___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_6773_, 0, v_toPure_6770_);
                leanh::lean_inc_ref(v___f_6773_);
                v___x_6774_ = leanh::lean_apply_4(
                    v_toBind_6769_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_getEnv_6764_,
                    v___f_6773_,
                );
                if v_isShared_6768_ == 0 {
                    leanh::lean_ctor_set(v___x_6767_, 1, v___f_6771_);
                    leanh::lean_ctor_set(v___x_6767_, 0, v___x_6774_);
                    v___x_6776_ = v___x_6767_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6802_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6802_, 0, v___x_6774_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6802_, 1, v___f_6771_);
                    v___x_6776_ = v_reuseFailAlloc_6802_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_toBind_6769_);
                v___x_6777_ = leanh::lean_apply_4(
                    v_toBind_6769_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_6744_,
                    v___f_6773_,
                );
                leanh::lean_inc_ref(v___x_6761_);
                v___x_6778_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_6761_, v_inst_6745_);
                v___f_6779_ = leanh::lean_alloc_closure(
                    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_6779_, 0, v_inst_6746_);
                leanh::lean_closure_set(v___f_6779_, 1, v___x_6761_);
                if leanh::lean_obj_tag(v_view_x3f_6749_) == 1 {
                    v_val_6789_ = leanh::lean_ctor_get(v_view_x3f_6749_, 0);
                    leanh::lean_inc(v_val_6789_);
                    leanh::lean_dec_ref_known(v_view_x3f_6749_, 1);
                    v_imported_6790_ = leanh::lean_ctor_get(v_val_6789_, 1);
                    v_ctx_6791_ = leanh::lean_ctor_get(v_val_6789_, 2);
                    v_scopes_6792_ = leanh::lean_ctor_get(v_val_6789_, 3);
                    v_isSharedCheck_6800_ = (!leanh::lean_is_exclusive(v_val_6789_)) as u8;
                    if v_isSharedCheck_6800_ == 0 {
                        v_unused_6801_ = leanh::lean_ctor_get(v_val_6789_, 0);
                        leanh::lean_dec(v_unused_6801_);
                        v___x_6794_ = v_val_6789_;
                        v_isShared_6795_ = v_isSharedCheck_6800_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_scopes_6792_);
                        leanh::lean_inc(v_ctx_6791_);
                        leanh::lean_inc(v_imported_6790_);
                        leanh::lean_dec(v_val_6789_);
                        v___x_6794_ = leanh::lean_box(0);
                        v_isShared_6795_ = v_isSharedCheck_6800_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_view_x3f_6749_);
                    v___y_6781_ = v_n_6750_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_n(v___y_6781_, 2);
                leanh::lean_inc_n(v_toPure_6770_, 3);
                v___f_6782_ = leanh::lean_alloc_closure(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1 as *mut core::ffi::c_void, 3, 2);
                leanh::lean_closure_set(v___f_6782_, 0, v_toPure_6770_);
                leanh::lean_closure_set(v___f_6782_, 1, v___y_6781_);
                leanh::lean_inc_n(v_toBind_6769_, 3);
                v___f_6783_ = leanh::lean_alloc_closure(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                leanh::lean_closure_set(v___f_6783_, 0, v_toPure_6770_);
                leanh::lean_closure_set(v___f_6783_, 1, v_toBind_6769_);
                leanh::lean_closure_set(v___f_6783_, 2, v___f_6782_);
                v___f_6784_ = leanh::lean_alloc_closure(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed as *mut core::ffi::c_void, 7, 6);
                leanh::lean_closure_set(v___f_6784_, 0, v_toPure_6770_);
                leanh::lean_closure_set(v___f_6784_, 1, v_filter_6748_);
                leanh::lean_closure_set(v___f_6784_, 2, v___y_6781_);
                leanh::lean_closure_set(v___f_6784_, 3, v_toBind_6769_);
                leanh::lean_closure_set(v___f_6784_, 4, v___f_6772_);
                leanh::lean_closure_set(v___f_6784_, 5, v___f_6783_);
                v___f_6785_ = leanh::lean_alloc_closure(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed as *mut core::ffi::c_void, 5, 4);
                leanh::lean_closure_set(v___f_6785_, 0, v_toPure_6770_);
                leanh::lean_closure_set(v___f_6785_, 1, v_n_u2080_6747_);
                leanh::lean_closure_set(v___f_6785_, 2, v_toBind_6769_);
                leanh::lean_closure_set(v___f_6785_, 3, v___f_6784_);
                v___x_6786_ = 0;
                v___x_6787_ = l_Lean_resolveGlobalName___redArg(
                    v___x_6760_,
                    v___x_6762_,
                    v___x_6776_,
                    v___x_6777_,
                    v___x_6778_,
                    v___f_6779_,
                    v___y_6781_,
                    v___x_6786_,
                );
                v___x_6788_ = leanh::lean_apply_4(
                    v_toBind_6769_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_6787_,
                    v___f_6785_,
                );
                return v___x_6788_;
            }
            4 => {
                if v_isShared_6795_ == 0 {
                    leanh::lean_ctor_set(v___x_6794_, 0, v_n_6750_);
                    v___x_6797_ = v___x_6794_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6799_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6799_, 0, v_n_6750_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6799_, 1, v_imported_6790_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6799_, 2, v_ctx_6791_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6799_, 3, v_scopes_6792_);
                    v___x_6797_ = v_reuseFailAlloc_6799_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6798_ = l_Lean_MacroScopesView_review(v___x_6797_);
                v___y_6781_ = v___x_6798_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve(
    mut v_m_6804_: *mut leanh::LeanObject,
    mut v_inst_6805_: *mut leanh::LeanObject,
    mut v_inst_6806_: *mut leanh::LeanObject,
    mut v_inst_6807_: *mut leanh::LeanObject,
    mut v_inst_6808_: *mut leanh::LeanObject,
    mut v_inst_6809_: *mut leanh::LeanObject,
    mut v_inst_6810_: *mut leanh::LeanObject,
    mut v_n_u2080_6811_: *mut leanh::LeanObject,
    mut v_filter_6812_: *mut leanh::LeanObject,
    mut v_view_x3f_6813_: *mut leanh::LeanObject,
    mut v_n_6814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6815_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(
        v_inst_6805_,
        v_inst_6806_,
        v_inst_6807_,
        v_inst_6808_,
        v_inst_6809_,
        v_inst_6810_,
        v_n_u2080_6811_,
        v_filter_6812_,
        v_view_x3f_6813_,
        v_n_6814_,
    );
    return v___x_6815_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0(
    mut v_toPure_6820_: *mut leanh::LeanObject,
    mut v_____x_6821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____x_6821_) == 0 {
        let mut v___x_6822_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6823_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6822_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__1;
        v___x_6823_ =
            leanh::lean_apply_2(v_toPure_6820_, leanh::lean_box(0), v___x_6822_);
        return v___x_6823_;
    } else {
        let mut v___x_6824_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6824_ =
            leanh::lean_apply_2(v_toPure_6820_, leanh::lean_box(0), v_____x_6821_);
        return v___x_6824_;
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1(
    mut v_toPure_6825_: *mut leanh::LeanObject,
    mut v_____do__lift_6826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6832_: u8 = 0;
    let mut v___x_6833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6838_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_6826_) == 0 {
                    v___x_6827_ = leanh::lean_box(0);
                    v___x_6828_ = leanh::lean_apply_2(
                        v_toPure_6825_,
                        leanh::lean_box(0),
                        v___x_6827_,
                    );
                    return v___x_6828_;
                } else {
                    v_val_6829_ = leanh::lean_ctor_get(v_____do__lift_6826_, 0);
                    v_isSharedCheck_6838_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_6826_)) as u8;
                    if v_isSharedCheck_6838_ == 0 {
                        v___x_6831_ = v_____do__lift_6826_;
                        v_isShared_6832_ = v_isSharedCheck_6838_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6829_);
                        leanh::lean_dec(v_____do__lift_6826_);
                        v___x_6831_ = leanh::lean_box(0);
                        v_isShared_6832_ = v_isSharedCheck_6838_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6833_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6833_, 0, v_val_6829_);
                if v_isShared_6832_ == 0 {
                    leanh::lean_ctor_set(v___x_6831_, 0, v___x_6833_);
                    v___x_6835_ = v___x_6831_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6837_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6837_, 0, v___x_6833_);
                    v___x_6835_ = v_reuseFailAlloc_6837_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6836_ = leanh::lean_apply_2(
                    v_toPure_6825_,
                    leanh::lean_box(0),
                    v___x_6835_,
                );
                return v___x_6836_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2(
    mut v_toPure_6839_: *mut leanh::LeanObject,
    mut v___x_6840_: *mut leanh::LeanObject,
    mut v_____do__lift_6841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_6841_) == 0 {
        let mut v___x_6842_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6842_ =
            leanh::lean_apply_2(v_toPure_6839_, leanh::lean_box(0), v___x_6840_);
        return v___x_6842_;
    } else {
        let mut v_val_6843_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_6844_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6845_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_6840_);
        v_val_6843_ = leanh::lean_ctor_get(v_____do__lift_6841_, 0);
        leanh::lean_inc(v_val_6843_);
        leanh::lean_dec_ref_known(v_____do__lift_6841_, 1);
        v_fst_6844_ = leanh::lean_ctor_get(v_val_6843_, 0);
        leanh::lean_inc(v_fst_6844_);
        leanh::lean_dec(v_val_6843_);
        v___x_6845_ =
            leanh::lean_apply_2(v_toPure_6839_, leanh::lean_box(0), v_fst_6844_);
        return v___x_6845_;
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3(
    mut v_toPure_6846_: *mut leanh::LeanObject,
    mut v___x_6847_: *mut leanh::LeanObject,
    mut v___x_6848_: *mut leanh::LeanObject,
    mut v_____do__lift_6849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6855_: u8 = 0;
    let mut v_a_6856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6859_: u8 = 0;
    let mut v___x_6861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6869_: u8 = 0;
    let mut v___x_6871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6872_: u8 = 0;
    let mut v___x_6873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6881_: u8 = 0;
    let mut v_unused_6882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_6849_) == 0 {
                    leanh::lean_dec(v___x_6848_);
                    leanh::lean_dec(v___x_6847_);
                    v___x_6850_ = leanh::lean_box(0);
                    v___x_6851_ = leanh::lean_apply_2(
                        v_toPure_6846_,
                        leanh::lean_box(0),
                        v___x_6850_,
                    );
                    return v___x_6851_;
                } else {
                    v_val_6852_ = leanh::lean_ctor_get(v_____do__lift_6849_, 0);
                    v_isSharedCheck_6883_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_6849_)) as u8;
                    if v_isSharedCheck_6883_ == 0 {
                        v___x_6854_ = v_____do__lift_6849_;
                        v_isShared_6855_ = v_isSharedCheck_6883_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6852_);
                        leanh::lean_dec(v_____do__lift_6849_);
                        v___x_6854_ = leanh::lean_box(0);
                        v_isShared_6855_ = v_isSharedCheck_6883_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_val_6852_) == 0 {
                    leanh::lean_dec(v___x_6848_);
                    v_a_6856_ = leanh::lean_ctor_get(v_val_6852_, 0);
                    v_isSharedCheck_6869_ = (!leanh::lean_is_exclusive(v_val_6852_)) as u8;
                    if v_isSharedCheck_6869_ == 0 {
                        v___x_6858_ = v_val_6852_;
                        v_isShared_6859_ = v_isSharedCheck_6869_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6856_);
                        leanh::lean_dec(v_val_6852_);
                        v___x_6858_ = leanh::lean_box(0);
                        v_isShared_6859_ = v_isSharedCheck_6869_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_isSharedCheck_6881_ = (!leanh::lean_is_exclusive(v_val_6852_)) as u8;
                    if v_isSharedCheck_6881_ == 0 {
                        v_unused_6882_ = leanh::lean_ctor_get(v_val_6852_, 0);
                        leanh::lean_dec(v_unused_6882_);
                        v___x_6871_ = v_val_6852_;
                        v_isShared_6872_ = v_isSharedCheck_6881_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v_val_6852_);
                        v___x_6871_ = leanh::lean_box(0);
                        v_isShared_6872_ = v_isSharedCheck_6881_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6855_ == 0 {
                    leanh::lean_ctor_set(v___x_6854_, 0, v_a_6856_);
                    v___x_6861_ = v___x_6854_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6868_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6868_, 0, v_a_6856_);
                    v___x_6861_ = v_reuseFailAlloc_6868_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6862_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6862_, 0, v___x_6861_);
                leanh::lean_ctor_set(v___x_6862_, 1, v___x_6847_);
                if v_isShared_6859_ == 0 {
                    leanh::lean_ctor_set(v___x_6858_, 0, v___x_6862_);
                    v___x_6864_ = v___x_6858_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6867_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6867_, 0, v___x_6862_);
                    v___x_6864_ = v_reuseFailAlloc_6867_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6865_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6865_, 0, v___x_6864_);
                v___x_6866_ = leanh::lean_apply_2(
                    v_toPure_6846_,
                    leanh::lean_box(0),
                    v___x_6865_,
                );
                return v___x_6866_;
            }
            5 => {
                v___x_6873_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6873_, 0, v___x_6848_);
                leanh::lean_ctor_set(v___x_6873_, 1, v___x_6847_);
                if v_isShared_6872_ == 0 {
                    leanh::lean_ctor_set(v___x_6871_, 0, v___x_6873_);
                    v___x_6875_ = v___x_6871_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6880_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6880_, 0, v___x_6873_);
                    v___x_6875_ = v_reuseFailAlloc_6880_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6855_ == 0 {
                    leanh::lean_ctor_set(v___x_6854_, 0, v___x_6875_);
                    v___x_6877_ = v___x_6854_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6879_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6879_, 0, v___x_6875_);
                    v___x_6877_ = v_reuseFailAlloc_6879_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_6878_ = leanh::lean_apply_2(
                    v_toPure_6846_,
                    leanh::lean_box(0),
                    v___x_6877_,
                );
                return v___x_6878_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(
    mut v_toPure_6884_: *mut leanh::LeanObject,
    mut v___x_6885_: *mut leanh::LeanObject,
    mut v_inst_6886_: *mut leanh::LeanObject,
    mut v_inst_6887_: *mut leanh::LeanObject,
    mut v_inst_6888_: *mut leanh::LeanObject,
    mut v_inst_6889_: *mut leanh::LeanObject,
    mut v_inst_6890_: *mut leanh::LeanObject,
    mut v_inst_6891_: *mut leanh::LeanObject,
    mut v_n_u2080_6892_: *mut leanh::LeanObject,
    mut v_filter_6893_: *mut leanh::LeanObject,
    mut v_view_x3f_6894_: *mut leanh::LeanObject,
    mut v_toBind_6895_: *mut leanh::LeanObject,
    mut v___f_6896_: *mut leanh::LeanObject,
    mut v___f_6897_: *mut leanh::LeanObject,
    mut v_a_6898_: *mut leanh::LeanObject,
    mut v_x_6899_: *mut leanh::LeanObject,
    mut v___y_6900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_6901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_6901_ = leanh::lean_ctor_get(v___y_6900_, 1);
    leanh::lean_inc(v_snd_6901_);
    leanh::lean_dec_ref(v___y_6900_);
    v___x_6902_ = l_Lean_Name_appendCore(v_a_6898_, v_snd_6901_);
    leanh::lean_inc(v___x_6902_);
    v___f_6903_ = leanh::lean_alloc_closure(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3 as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___f_6903_, 0, v_toPure_6884_);
    leanh::lean_closure_set(v___f_6903_, 1, v___x_6902_);
    leanh::lean_closure_set(v___f_6903_, 2, v___x_6885_);
    v___x_6904_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(
        v_inst_6886_,
        v_inst_6887_,
        v_inst_6888_,
        v_inst_6889_,
        v_inst_6890_,
        v_inst_6891_,
        v_n_u2080_6892_,
        v_filter_6893_,
        v_view_x3f_6894_,
        v___x_6902_,
    );
    leanh::lean_inc_n(v_toBind_6895_, 2);
    v___x_6905_ = leanh::lean_apply_4(
        v_toBind_6895_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6904_,
        v___f_6896_,
    );
    v___x_6906_ = leanh::lean_apply_4(
        v_toBind_6895_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6905_,
        v___f_6897_,
    );
    v___x_6907_ = leanh::lean_apply_4(
        v_toBind_6895_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6906_,
        v___f_6903_,
    );
    return v___x_6907_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_6908_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_6909_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_inst_6910_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_inst_6911_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_inst_6912_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_inst_6913_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_inst_6914_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_inst_6915_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_n_u2080_6916_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_filter_6917_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_view_x3f_6918_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_toBind_6919_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___f_6920_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___f_6921_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_6922_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_x_6923_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_6924_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_res_6925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6925_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(v_toPure_6908_, v___x_6909_, v_inst_6910_, v_inst_6911_, v_inst_6912_, v_inst_6913_, v_inst_6914_, v_inst_6915_, v_n_u2080_6916_, v_filter_6917_, v_view_x3f_6918_, v_toBind_6919_, v___f_6920_, v___f_6921_, v_a_6922_, v_x_6923_, v___y_6924_);
    leanh::lean_dec(v_a_6922_);
    return v_res_6925_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(
    mut v_toPure_6929_: *mut leanh::LeanObject,
    mut v_n_6930_: *mut leanh::LeanObject,
    mut v_inst_6931_: *mut leanh::LeanObject,
    mut v_inst_6932_: *mut leanh::LeanObject,
    mut v_inst_6933_: *mut leanh::LeanObject,
    mut v_inst_6934_: *mut leanh::LeanObject,
    mut v_inst_6935_: *mut leanh::LeanObject,
    mut v_inst_6936_: *mut leanh::LeanObject,
    mut v_n_u2080_6937_: *mut leanh::LeanObject,
    mut v_filter_6938_: *mut leanh::LeanObject,
    mut v_view_x3f_6939_: *mut leanh::LeanObject,
    mut v_toBind_6940_: *mut leanh::LeanObject,
    mut v___f_6941_: *mut leanh::LeanObject,
    mut v___f_6942_: *mut leanh::LeanObject,
    mut v___x_6943_: *mut leanh::LeanObject,
    mut v_____do__lift_6944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_6944_) == 0 {
        let mut v___x_6945_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6946_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_6943_);
        leanh::lean_dec(v___f_6942_);
        leanh::lean_dec(v___f_6941_);
        leanh::lean_dec(v_toBind_6940_);
        leanh::lean_dec(v_view_x3f_6939_);
        leanh::lean_dec(v_filter_6938_);
        leanh::lean_dec(v_n_u2080_6937_);
        leanh::lean_dec(v_inst_6936_);
        leanh::lean_dec_ref(v_inst_6935_);
        leanh::lean_dec(v_inst_6934_);
        leanh::lean_dec_ref(v_inst_6933_);
        leanh::lean_dec_ref(v_inst_6932_);
        leanh::lean_dec_ref(v_inst_6931_);
        leanh::lean_dec(v_n_6930_);
        v___x_6945_ = leanh::lean_box(0);
        v___x_6946_ =
            leanh::lean_apply_2(v_toPure_6929_, leanh::lean_box(0), v___x_6945_);
        return v___x_6946_;
    } else {
        let mut v___x_6947_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6948_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6949_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6950_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6951_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6952_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6953_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6954_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6947_ = l_Lean_privateToUserName(v_n_6930_);
        v___x_6948_ = l_Lean_Name_componentsRev(v___x_6947_);
        v___x_6949_ = leanh::lean_box(0);
        leanh::lean_inc(v_toPure_6929_);
        v___f_6950_ = leanh::lean_alloc_closure(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2 as *mut core::ffi::c_void, 3, 2);
        leanh::lean_closure_set(v___f_6950_, 0, v_toPure_6929_);
        leanh::lean_closure_set(v___f_6950_, 1, v___x_6949_);
        leanh::lean_inc(v_toBind_6940_);
        v___f_6951_ = leanh::lean_alloc_closure(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed as *mut core::ffi::c_void, 17, 14);
        leanh::lean_closure_set(v___f_6951_, 0, v_toPure_6929_);
        leanh::lean_closure_set(v___f_6951_, 1, v___x_6949_);
        leanh::lean_closure_set(v___f_6951_, 2, v_inst_6931_);
        leanh::lean_closure_set(v___f_6951_, 3, v_inst_6932_);
        leanh::lean_closure_set(v___f_6951_, 4, v_inst_6933_);
        leanh::lean_closure_set(v___f_6951_, 5, v_inst_6934_);
        leanh::lean_closure_set(v___f_6951_, 6, v_inst_6935_);
        leanh::lean_closure_set(v___f_6951_, 7, v_inst_6936_);
        leanh::lean_closure_set(v___f_6951_, 8, v_n_u2080_6937_);
        leanh::lean_closure_set(v___f_6951_, 9, v_filter_6938_);
        leanh::lean_closure_set(v___f_6951_, 10, v_view_x3f_6939_);
        leanh::lean_closure_set(v___f_6951_, 11, v_toBind_6940_);
        leanh::lean_closure_set(v___f_6951_, 12, v___f_6941_);
        leanh::lean_closure_set(v___f_6951_, 13, v___f_6942_);
        v___x_6952_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___closed__0;
        v___x_6953_ =
            l_List_forIn_x27_loop___redArg(v___x_6943_, v___f_6951_, v___x_6948_, v___x_6952_);
        leanh::lean_dec(v___x_6948_);
        v___x_6954_ = leanh::lean_apply_4(
            v_toBind_6940_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_6953_,
            v___f_6950_,
        );
        return v___x_6954_;
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed(
    mut v_toPure_6955_: *mut leanh::LeanObject,
    mut v_n_6956_: *mut leanh::LeanObject,
    mut v_inst_6957_: *mut leanh::LeanObject,
    mut v_inst_6958_: *mut leanh::LeanObject,
    mut v_inst_6959_: *mut leanh::LeanObject,
    mut v_inst_6960_: *mut leanh::LeanObject,
    mut v_inst_6961_: *mut leanh::LeanObject,
    mut v_inst_6962_: *mut leanh::LeanObject,
    mut v_n_u2080_6963_: *mut leanh::LeanObject,
    mut v_filter_6964_: *mut leanh::LeanObject,
    mut v_view_x3f_6965_: *mut leanh::LeanObject,
    mut v_toBind_6966_: *mut leanh::LeanObject,
    mut v___f_6967_: *mut leanh::LeanObject,
    mut v___f_6968_: *mut leanh::LeanObject,
    mut v___x_6969_: *mut leanh::LeanObject,
    mut v_____do__lift_6970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6971_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(v_toPure_6955_, v_n_6956_, v_inst_6957_, v_inst_6958_, v_inst_6959_, v_inst_6960_, v_inst_6961_, v_inst_6962_, v_n_u2080_6963_, v_filter_6964_, v_view_x3f_6965_, v_toBind_6966_, v___f_6967_, v___f_6968_, v___x_6969_, v_____do__lift_6970_);
    leanh::lean_dec(v_____do__lift_6970_);
    return v_res_6971_;
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(
    mut v_inst_6972_: *mut leanh::LeanObject,
    mut v_inst_6973_: *mut leanh::LeanObject,
    mut v_inst_6974_: *mut leanh::LeanObject,
    mut v_inst_6975_: *mut leanh::LeanObject,
    mut v_inst_6976_: *mut leanh::LeanObject,
    mut v_inst_6977_: *mut leanh::LeanObject,
    mut v_n_u2080_6978_: *mut leanh::LeanObject,
    mut v_filter_6979_: *mut leanh::LeanObject,
    mut v_view_x3f_6980_: *mut leanh::LeanObject,
    mut v_n_6981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7001_: u8 = 0;
    let mut v_toApplicative_7002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_7006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref_n(v_inst_6972_, 7);
                v___f_6982_ = leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                leanh::lean_closure_set(v___f_6982_, 0, v_inst_6972_);
                v___f_6983_ = leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                leanh::lean_closure_set(v___f_6983_, 0, v_inst_6972_);
                v___f_6984_ = leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__6 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                leanh::lean_closure_set(v___f_6984_, 0, v_inst_6972_);
                v___f_6985_ = leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                leanh::lean_closure_set(v___f_6985_, 0, v_inst_6972_);
                v___f_6986_ = leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__11 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                leanh::lean_closure_set(v___f_6986_, 0, v_inst_6972_);
                v___x_6987_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6987_, 0, v___f_6982_);
                leanh::lean_ctor_set(v___x_6987_, 1, v___f_6983_);
                v___x_6988_ = leanh::lean_alloc_closure(
                    l_OptionT_pure as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___x_6988_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_6988_, 1, v_inst_6972_);
                v___x_6989_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_6989_, 0, v___x_6987_);
                leanh::lean_ctor_set(v___x_6989_, 1, v___x_6988_);
                leanh::lean_ctor_set(v___x_6989_, 2, v___f_6984_);
                leanh::lean_ctor_set(v___x_6989_, 3, v___f_6985_);
                leanh::lean_ctor_set(v___x_6989_, 4, v___f_6986_);
                v___x_6990_ = leanh::lean_alloc_closure(
                    l_OptionT_bind as *mut core::ffi::c_void,
                    6,
                    2,
                );
                leanh::lean_closure_set(v___x_6990_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_6990_, 1, v_inst_6972_);
                v___x_6991_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6991_, 0, v___x_6989_);
                leanh::lean_ctor_set(v___x_6991_, 1, v___x_6990_);
                v___x_7001_ = l_Lean_Name_hasMacroScopes(v_n_6981_);
                if v___x_7001_ == 0 {
                    v_toApplicative_7002_ = leanh::lean_ctor_get(v_inst_6972_, 0);
                    v_toPure_7003_ = leanh::lean_ctor_get(v_toApplicative_7002_, 1);
                    v___x_7004_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0;
                    leanh::lean_inc(v_toPure_7003_);
                    v___x_7005_ = leanh::lean_apply_2(
                        v_toPure_7003_,
                        leanh::lean_box(0),
                        v___x_7004_,
                    );
                    v___y_6993_ = v___x_7005_;
                    state = 1;
                    continue;
                } else {
                    v_toApplicative_7006_ = leanh::lean_ctor_get(v_inst_6972_, 0);
                    v_toPure_7007_ = leanh::lean_ctor_get(v_toApplicative_7006_, 1);
                    v___x_7008_ = leanh::lean_box(0);
                    leanh::lean_inc(v_toPure_7007_);
                    v___x_7009_ = leanh::lean_apply_2(
                        v_toPure_7007_,
                        leanh::lean_box(0),
                        v___x_7008_,
                    );
                    v___y_6993_ = v___x_7009_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toApplicative_6994_ = leanh::lean_ctor_get(v_inst_6972_, 0);
                v_toBind_6995_ = leanh::lean_ctor_get(v_inst_6972_, 1);
                leanh::lean_inc_n(v_toBind_6995_, 2);
                v_toPure_6996_ = leanh::lean_ctor_get(v_toApplicative_6994_, 1);
                leanh::lean_inc_n(v_toPure_6996_, 3);
                v___f_6997_ = leanh::lean_alloc_closure(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_6997_, 0, v_toPure_6996_);
                v___f_6998_ = leanh::lean_alloc_closure(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_6998_, 0, v_toPure_6996_);
                v___f_6999_ = leanh::lean_alloc_closure(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed as *mut core::ffi::c_void, 16, 15);
                leanh::lean_closure_set(v___f_6999_, 0, v_toPure_6996_);
                leanh::lean_closure_set(v___f_6999_, 1, v_n_6981_);
                leanh::lean_closure_set(v___f_6999_, 2, v_inst_6972_);
                leanh::lean_closure_set(v___f_6999_, 3, v_inst_6973_);
                leanh::lean_closure_set(v___f_6999_, 4, v_inst_6974_);
                leanh::lean_closure_set(v___f_6999_, 5, v_inst_6975_);
                leanh::lean_closure_set(v___f_6999_, 6, v_inst_6976_);
                leanh::lean_closure_set(v___f_6999_, 7, v_inst_6977_);
                leanh::lean_closure_set(v___f_6999_, 8, v_n_u2080_6978_);
                leanh::lean_closure_set(v___f_6999_, 9, v_filter_6979_);
                leanh::lean_closure_set(v___f_6999_, 10, v_view_x3f_6980_);
                leanh::lean_closure_set(v___f_6999_, 11, v_toBind_6995_);
                leanh::lean_closure_set(v___f_6999_, 12, v___f_6998_);
                leanh::lean_closure_set(v___f_6999_, 13, v___f_6997_);
                leanh::lean_closure_set(v___f_6999_, 14, v___x_6991_);
                v___x_7000_ = leanh::lean_apply_4(
                    v_toBind_6995_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___y_6993_,
                    v___f_6999_,
                );
                return v___x_7000_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore(
    mut v_m_7010_: *mut leanh::LeanObject,
    mut v_inst_7011_: *mut leanh::LeanObject,
    mut v_inst_7012_: *mut leanh::LeanObject,
    mut v_inst_7013_: *mut leanh::LeanObject,
    mut v_inst_7014_: *mut leanh::LeanObject,
    mut v_inst_7015_: *mut leanh::LeanObject,
    mut v_inst_7016_: *mut leanh::LeanObject,
    mut v_n_u2080_7017_: *mut leanh::LeanObject,
    mut v_filter_7018_: *mut leanh::LeanObject,
    mut v_view_x3f_7019_: *mut leanh::LeanObject,
    mut v_n_7020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7021_ =
        l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(
            v_inst_7011_,
            v_inst_7012_,
            v_inst_7013_,
            v_inst_7014_,
            v_inst_7015_,
            v_inst_7016_,
            v_n_u2080_7017_,
            v_filter_7018_,
            v_view_x3f_7019_,
            v_n_7020_,
        );
    return v___x_7021_;
}
pub unsafe fn l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(
    mut v_n_u2081_7022_: *mut leanh::LeanObject,
    mut v_x1_7023_: *mut leanh::LeanObject,
    mut v_x2_7024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7027_: u8 = 0;
    v___x_7025_ = l_Lean_Name_getPrefix(v_x2_7024_);
    v___x_7026_ = l_Lean_Name_getPrefix(v_n_u2081_7022_);
    v___x_7027_ = l_Lean_Name_isPrefixOf(v___x_7025_, v___x_7026_);
    leanh::lean_dec(v___x_7026_);
    leanh::lean_dec(v___x_7025_);
    if v___x_7027_ == 0 {
        leanh::lean_dec(v_x2_7024_);
        return v_x1_7023_;
    } else {
        let mut v___x_7028_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_7028_ = lean_array_push(v_x1_7023_, v_x2_7024_);
        return v___x_7028_;
    }
}
pub unsafe fn l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed(
    mut v_n_u2081_7029_: *mut leanh::LeanObject,
    mut v_x1_7030_: *mut leanh::LeanObject,
    mut v_x2_7031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7032_ =
        l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(v_n_u2081_7029_, v_x1_7030_, v_x2_7031_);
    leanh::lean_dec(v_n_u2081_7029_);
    return v_res_7032_;
}
pub unsafe fn l_Lean_unresolveNameGlobal_x3f___redArg___lam__1(
    mut v_view_7033_: *mut leanh::LeanObject,
    mut v_n_u2081_7034_: *mut leanh::LeanObject,
    mut v_inst_7035_: *mut leanh::LeanObject,
    mut v_inst_7036_: *mut leanh::LeanObject,
    mut v_inst_7037_: *mut leanh::LeanObject,
    mut v_inst_7038_: *mut leanh::LeanObject,
    mut v_inst_7039_: *mut leanh::LeanObject,
    mut v_inst_7040_: *mut leanh::LeanObject,
    mut v_n_u2080_7041_: *mut leanh::LeanObject,
    mut v_filter_7042_: *mut leanh::LeanObject,
    mut v_toPure_7043_: *mut leanh::LeanObject,
    mut v_____do__lift_7044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_7044_) == 0 {
        let mut v___x_7045_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7046_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7047_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7048_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_7043_);
        v___x_7045_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_7045_, 0, v_view_7033_);
        v___x_7046_ = l_Lean_rootNamespace;
        v___x_7047_ = l_Lean_Name_append(v___x_7046_, v_n_u2081_7034_);
        v___x_7048_ =
            l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(
                v_inst_7035_,
                v_inst_7036_,
                v_inst_7037_,
                v_inst_7038_,
                v_inst_7039_,
                v_inst_7040_,
                v_n_u2080_7041_,
                v_filter_7042_,
                v___x_7045_,
                v___x_7047_,
            );
        return v___x_7048_;
    } else {
        let mut v___x_7049_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_filter_7042_);
        leanh::lean_dec(v_n_u2080_7041_);
        leanh::lean_dec(v_inst_7040_);
        leanh::lean_dec_ref(v_inst_7039_);
        leanh::lean_dec(v_inst_7038_);
        leanh::lean_dec_ref(v_inst_7037_);
        leanh::lean_dec_ref(v_inst_7036_);
        leanh::lean_dec_ref(v_inst_7035_);
        leanh::lean_dec(v_n_u2081_7034_);
        leanh::lean_dec_ref(v_view_7033_);
        v___x_7049_ = leanh::lean_apply_2(
            v_toPure_7043_,
            leanh::lean_box(0),
            v_____do__lift_7044_,
        );
        return v___x_7049_;
    }
}
pub unsafe fn l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(
    mut v_toPure_7050_: *mut leanh::LeanObject,
    mut v_inst_7051_: *mut leanh::LeanObject,
    mut v_inst_7052_: *mut leanh::LeanObject,
    mut v_inst_7053_: *mut leanh::LeanObject,
    mut v_inst_7054_: *mut leanh::LeanObject,
    mut v_inst_7055_: *mut leanh::LeanObject,
    mut v_inst_7056_: *mut leanh::LeanObject,
    mut v_n_u2080_7057_: *mut leanh::LeanObject,
    mut v_filter_7058_: *mut leanh::LeanObject,
    mut v_toBind_7059_: *mut leanh::LeanObject,
    mut v___f_7060_: *mut leanh::LeanObject,
    mut v_allowHorizAliases_7061_: u8,
    mut v___f_7062_: *mut leanh::LeanObject,
    mut v_____do__lift_7063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_aliases_7065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7081_: u8 = 0;
    let mut v___x_7082_: u8 = 0;
    let mut v___x_7083_: usize = 0;
    let mut v___x_7084_: usize = 0;
    let mut v___x_7085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7086_: usize = 0;
    let mut v___x_7087_: usize = 0;
    let mut v___x_7088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_7063_) == 0 {
                    leanh::lean_dec_ref(v___f_7062_);
                    leanh::lean_dec(v___f_7060_);
                    leanh::lean_dec(v_toBind_7059_);
                    leanh::lean_dec(v_filter_7058_);
                    leanh::lean_dec(v_n_u2080_7057_);
                    leanh::lean_dec(v_inst_7056_);
                    leanh::lean_dec_ref(v_inst_7055_);
                    leanh::lean_dec(v_inst_7054_);
                    leanh::lean_dec_ref(v_inst_7053_);
                    leanh::lean_dec_ref(v_inst_7052_);
                    leanh::lean_dec_ref(v_inst_7051_);
                    v___x_7072_ = leanh::lean_box(0);
                    v___x_7073_ = leanh::lean_apply_2(
                        v_toPure_7050_,
                        leanh::lean_box(0),
                        v___x_7072_,
                    );
                    return v___x_7073_;
                } else {
                    leanh::lean_dec(v_toPure_7050_);
                    v_val_7074_ = leanh::lean_ctor_get(v_____do__lift_7063_, 0);
                    leanh::lean_inc(v_val_7074_);
                    leanh::lean_dec_ref_known(v_____do__lift_7063_, 1);
                    leanh::lean_inc(v_n_u2080_7057_);
                    v___x_7075_ = l_Lean_getRevAliases(v_val_7074_, v_n_u2080_7057_);
                    v___x_7076_ = lean_array_mk(v___x_7075_);
                    if v_allowHorizAliases_7061_ == 0 {
                        v___x_7077_ = leanh::lean_unsigned_to_nat(0);
                        v___x_7078_ = lean_array_get_size(v___x_7076_);
                        v___x_7079_ = l_Lean_resolveNamespace___redArg___closed__1;
                        v___x_7080_ = l_Lean_resolveLocalName___redArg___lam__3___closed__9;
                        v___x_7081_ = lean_nat_dec_lt(v___x_7077_, v___x_7078_);
                        if v___x_7081_ == 0 {
                            leanh::lean_dec_ref(v___x_7076_);
                            leanh::lean_dec_ref(v___f_7062_);
                            v_aliases_7065_ = v___x_7079_;
                            state = 1;
                            continue;
                        } else {
                            v___x_7082_ = lean_nat_dec_le(v___x_7078_, v___x_7078_);
                            if v___x_7082_ == 0 {
                                if v___x_7081_ == 0 {
                                    leanh::lean_dec_ref(v___x_7076_);
                                    leanh::lean_dec_ref(v___f_7062_);
                                    v_aliases_7065_ = v___x_7079_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_7083_ = 0usize;
                                    v___x_7084_ = lean_usize_of_nat(v___x_7078_);
                                    v___x_7085_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_7080_, v___f_7062_, v___x_7076_, v___x_7083_, v___x_7084_, v___x_7079_);
                                    v_aliases_7065_ = v___x_7085_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___x_7086_ = 0usize;
                                v___x_7087_ = lean_usize_of_nat(v___x_7078_);
                                v___x_7088_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        v___x_7080_,
                                        v___f_7062_,
                                        v___x_7076_,
                                        v___x_7086_,
                                        v___x_7087_,
                                        v___x_7079_,
                                    );
                                v_aliases_7065_ = v___x_7088_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___f_7062_);
                        v_aliases_7065_ = v___x_7076_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_7051_);
                v___x_7066_ = l_OptionT_instAlternative___redArg(v_inst_7051_);
                v___x_7067_ = leanh::lean_box(0);
                v___x_7068_ = leanh::lean_alloc_closure(
                    l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore
                        as *mut core::ffi::c_void,
                    11,
                    10,
                );
                leanh::lean_closure_set(v___x_7068_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_7068_, 1, v_inst_7051_);
                leanh::lean_closure_set(v___x_7068_, 2, v_inst_7052_);
                leanh::lean_closure_set(v___x_7068_, 3, v_inst_7053_);
                leanh::lean_closure_set(v___x_7068_, 4, v_inst_7054_);
                leanh::lean_closure_set(v___x_7068_, 5, v_inst_7055_);
                leanh::lean_closure_set(v___x_7068_, 6, v_inst_7056_);
                leanh::lean_closure_set(v___x_7068_, 7, v_n_u2080_7057_);
                leanh::lean_closure_set(v___x_7068_, 8, v_filter_7058_);
                leanh::lean_closure_set(v___x_7068_, 9, v___x_7067_);
                v___x_7069_ = leanh::lean_unsigned_to_nat(0);
                v___x_7070_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_7066_,
                    v___x_7068_,
                    v_aliases_7065_,
                    v___x_7069_,
                );
                v___x_7071_ = leanh::lean_apply_4(
                    v_toBind_7059_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_7070_,
                    v___f_7060_,
                );
                return v___x_7071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed(
    mut v_toPure_7089_: *mut leanh::LeanObject,
    mut v_inst_7090_: *mut leanh::LeanObject,
    mut v_inst_7091_: *mut leanh::LeanObject,
    mut v_inst_7092_: *mut leanh::LeanObject,
    mut v_inst_7093_: *mut leanh::LeanObject,
    mut v_inst_7094_: *mut leanh::LeanObject,
    mut v_inst_7095_: *mut leanh::LeanObject,
    mut v_n_u2080_7096_: *mut leanh::LeanObject,
    mut v_filter_7097_: *mut leanh::LeanObject,
    mut v_toBind_7098_: *mut leanh::LeanObject,
    mut v___f_7099_: *mut leanh::LeanObject,
    mut v_allowHorizAliases_7100_: *mut leanh::LeanObject,
    mut v___f_7101_: *mut leanh::LeanObject,
    mut v_____do__lift_7102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowHorizAliases_boxed_7103_: u8 = 0;
    let mut v_res_7104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowHorizAliases_boxed_7103_ = (leanh::lean_unbox(v_allowHorizAliases_7100_) as u8);
    v_res_7104_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(
        v_toPure_7089_,
        v_inst_7090_,
        v_inst_7091_,
        v_inst_7092_,
        v_inst_7093_,
        v_inst_7094_,
        v_inst_7095_,
        v_n_u2080_7096_,
        v_filter_7097_,
        v_toBind_7098_,
        v___f_7099_,
        v_allowHorizAliases_boxed_7103_,
        v___f_7101_,
        v_____do__lift_7102_,
    );
    return v_res_7104_;
}
pub unsafe fn l_Lean_unresolveNameGlobal_x3f___redArg___lam__3(
    mut v_toPure_7105_: *mut leanh::LeanObject,
    mut v_____do__lift_7106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7107_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7107_, 0, v_____do__lift_7106_);
    v___x_7108_ =
        leanh::lean_apply_2(v_toPure_7105_, leanh::lean_box(0), v___x_7107_);
    return v___x_7108_;
}
pub unsafe fn l_Lean_unresolveNameGlobal_x3f___redArg___lam__4(
    mut v_n_u2081_7109_: *mut leanh::LeanObject,
    mut v_inst_7110_: *mut leanh::LeanObject,
    mut v_inst_7111_: *mut leanh::LeanObject,
    mut v_inst_7112_: *mut leanh::LeanObject,
    mut v_inst_7113_: *mut leanh::LeanObject,
    mut v_inst_7114_: *mut leanh::LeanObject,
    mut v_inst_7115_: *mut leanh::LeanObject,
    mut v_n_u2080_7116_: *mut leanh::LeanObject,
    mut v_filter_7117_: *mut leanh::LeanObject,
    mut v___x_7118_: *mut leanh::LeanObject,
    mut v_toPure_7119_: *mut leanh::LeanObject,
    mut v_____do__lift_7120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_7120_) == 0 {
        let mut v___x_7121_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7122_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7123_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_7119_);
        v___x_7121_ = l_Lean_rootNamespace;
        v___x_7122_ = l_Lean_Name_append(v___x_7121_, v_n_u2081_7109_);
        v___x_7123_ =
            l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(
                v_inst_7110_,
                v_inst_7111_,
                v_inst_7112_,
                v_inst_7113_,
                v_inst_7114_,
                v_inst_7115_,
                v_n_u2080_7116_,
                v_filter_7117_,
                v___x_7118_,
                v___x_7122_,
            );
        return v___x_7123_;
    } else {
        let mut v___x_7124_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_7118_);
        leanh::lean_dec(v_filter_7117_);
        leanh::lean_dec(v_n_u2080_7116_);
        leanh::lean_dec(v_inst_7115_);
        leanh::lean_dec_ref(v_inst_7114_);
        leanh::lean_dec(v_inst_7113_);
        leanh::lean_dec_ref(v_inst_7112_);
        leanh::lean_dec_ref(v_inst_7111_);
        leanh::lean_dec_ref(v_inst_7110_);
        leanh::lean_dec(v_n_u2081_7109_);
        v___x_7124_ = leanh::lean_apply_2(
            v_toPure_7119_,
            leanh::lean_box(0),
            v_____do__lift_7120_,
        );
        return v___x_7124_;
    }
}
pub unsafe fn l_Lean_unresolveNameGlobal_x3f___redArg(
    mut v_inst_7125_: *mut leanh::LeanObject,
    mut v_inst_7126_: *mut leanh::LeanObject,
    mut v_inst_7127_: *mut leanh::LeanObject,
    mut v_inst_7128_: *mut leanh::LeanObject,
    mut v_inst_7129_: *mut leanh::LeanObject,
    mut v_inst_7130_: *mut leanh::LeanObject,
    mut v_n_u2080_7131_: *mut leanh::LeanObject,
    mut v_fullNames_7132_: u8,
    mut v_allowHorizAliases_7133_: u8,
    mut v_filter_7134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_view_7135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_7136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_u2081_7137_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_n_u2080_7131_);
    v_view_7135_ = l_Lean_extractMacroScopes(v_n_u2080_7131_);
    v_name_7136_ = leanh::lean_ctor_get(v_view_7135_, 0);
    leanh::lean_inc(v_name_7136_);
    v_n_u2081_7137_ = l_Lean_privateToUserName(v_name_7136_);
    if v_fullNames_7132_ == 0 {
        let mut v_toApplicative_7138_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_7139_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_7140_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_7141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7142_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7143_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7144_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7145_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7146_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7147_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7148_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_7138_ = leanh::lean_ctor_get(v_inst_7125_, 0);
        v_getEnv_7139_ = leanh::lean_ctor_get(v_inst_7127_, 0);
        leanh::lean_inc(v_getEnv_7139_);
        v_toBind_7140_ = leanh::lean_ctor_get(v_inst_7125_, 1);
        leanh::lean_inc_n(v_toBind_7140_, 3);
        v_toPure_7141_ = leanh::lean_ctor_get(v_toApplicative_7138_, 1);
        leanh::lean_inc_n(v_toPure_7141_, 3);
        leanh::lean_inc(v_n_u2081_7137_);
        v___f_7142_ = leanh::lean_alloc_closure(
            l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_7142_, 0, v_n_u2081_7137_);
        leanh::lean_inc(v_filter_7134_);
        leanh::lean_inc(v_n_u2080_7131_);
        leanh::lean_inc(v_inst_7130_);
        leanh::lean_inc_ref(v_inst_7129_);
        leanh::lean_inc(v_inst_7128_);
        leanh::lean_inc_ref(v_inst_7127_);
        leanh::lean_inc_ref(v_inst_7126_);
        leanh::lean_inc_ref(v_inst_7125_);
        v___f_7143_ = leanh::lean_alloc_closure(
            l_Lean_unresolveNameGlobal_x3f___redArg___lam__1 as *mut core::ffi::c_void,
            12,
            11,
        );
        leanh::lean_closure_set(v___f_7143_, 0, v_view_7135_);
        leanh::lean_closure_set(v___f_7143_, 1, v_n_u2081_7137_);
        leanh::lean_closure_set(v___f_7143_, 2, v_inst_7125_);
        leanh::lean_closure_set(v___f_7143_, 3, v_inst_7126_);
        leanh::lean_closure_set(v___f_7143_, 4, v_inst_7127_);
        leanh::lean_closure_set(v___f_7143_, 5, v_inst_7128_);
        leanh::lean_closure_set(v___f_7143_, 6, v_inst_7129_);
        leanh::lean_closure_set(v___f_7143_, 7, v_inst_7130_);
        leanh::lean_closure_set(v___f_7143_, 8, v_n_u2080_7131_);
        leanh::lean_closure_set(v___f_7143_, 9, v_filter_7134_);
        leanh::lean_closure_set(v___f_7143_, 10, v_toPure_7141_);
        v___x_7144_ = leanh::lean_box((v_allowHorizAliases_7133_) as usize);
        v___f_7145_ = leanh::lean_alloc_closure(
            l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
            14,
            13,
        );
        leanh::lean_closure_set(v___f_7145_, 0, v_toPure_7141_);
        leanh::lean_closure_set(v___f_7145_, 1, v_inst_7125_);
        leanh::lean_closure_set(v___f_7145_, 2, v_inst_7126_);
        leanh::lean_closure_set(v___f_7145_, 3, v_inst_7127_);
        leanh::lean_closure_set(v___f_7145_, 4, v_inst_7128_);
        leanh::lean_closure_set(v___f_7145_, 5, v_inst_7129_);
        leanh::lean_closure_set(v___f_7145_, 6, v_inst_7130_);
        leanh::lean_closure_set(v___f_7145_, 7, v_n_u2080_7131_);
        leanh::lean_closure_set(v___f_7145_, 8, v_filter_7134_);
        leanh::lean_closure_set(v___f_7145_, 9, v_toBind_7140_);
        leanh::lean_closure_set(v___f_7145_, 10, v___f_7143_);
        leanh::lean_closure_set(v___f_7145_, 11, v___x_7144_);
        leanh::lean_closure_set(v___f_7145_, 12, v___f_7142_);
        v___f_7146_ = leanh::lean_alloc_closure(
            l_Lean_unresolveNameGlobal_x3f___redArg___lam__3 as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_7146_, 0, v_toPure_7141_);
        v___x_7147_ = leanh::lean_apply_4(
            v_toBind_7140_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_7139_,
            v___f_7146_,
        );
        v___x_7148_ = leanh::lean_apply_4(
            v_toBind_7140_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_7147_,
            v___f_7145_,
        );
        return v___x_7148_;
    } else {
        let mut v_toApplicative_7149_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_7150_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_7151_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7152_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7153_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7154_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7155_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_7149_ = leanh::lean_ctor_get(v_inst_7125_, 0);
        v_toBind_7150_ = leanh::lean_ctor_get(v_inst_7125_, 1);
        leanh::lean_inc(v_toBind_7150_);
        v_toPure_7151_ = leanh::lean_ctor_get(v_toApplicative_7149_, 1);
        leanh::lean_inc(v_toPure_7151_);
        v___x_7152_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_7152_, 0, v_view_7135_);
        leanh::lean_inc(v_n_u2081_7137_);
        leanh::lean_inc_ref(v___x_7152_);
        leanh::lean_inc(v_filter_7134_);
        leanh::lean_inc(v_n_u2080_7131_);
        leanh::lean_inc(v_inst_7130_);
        leanh::lean_inc_ref(v_inst_7129_);
        leanh::lean_inc(v_inst_7128_);
        leanh::lean_inc_ref(v_inst_7127_);
        leanh::lean_inc_ref(v_inst_7126_);
        leanh::lean_inc_ref(v_inst_7125_);
        v___x_7153_ =
            l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(
                v_inst_7125_,
                v_inst_7126_,
                v_inst_7127_,
                v_inst_7128_,
                v_inst_7129_,
                v_inst_7130_,
                v_n_u2080_7131_,
                v_filter_7134_,
                v___x_7152_,
                v_n_u2081_7137_,
            );
        v___f_7154_ = leanh::lean_alloc_closure(
            l_Lean_unresolveNameGlobal_x3f___redArg___lam__4 as *mut core::ffi::c_void,
            12,
            11,
        );
        leanh::lean_closure_set(v___f_7154_, 0, v_n_u2081_7137_);
        leanh::lean_closure_set(v___f_7154_, 1, v_inst_7125_);
        leanh::lean_closure_set(v___f_7154_, 2, v_inst_7126_);
        leanh::lean_closure_set(v___f_7154_, 3, v_inst_7127_);
        leanh::lean_closure_set(v___f_7154_, 4, v_inst_7128_);
        leanh::lean_closure_set(v___f_7154_, 5, v_inst_7129_);
        leanh::lean_closure_set(v___f_7154_, 6, v_inst_7130_);
        leanh::lean_closure_set(v___f_7154_, 7, v_n_u2080_7131_);
        leanh::lean_closure_set(v___f_7154_, 8, v_filter_7134_);
        leanh::lean_closure_set(v___f_7154_, 9, v___x_7152_);
        leanh::lean_closure_set(v___f_7154_, 10, v_toPure_7151_);
        v___x_7155_ = leanh::lean_apply_4(
            v_toBind_7150_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_7153_,
            v___f_7154_,
        );
        return v___x_7155_;
    }
}
pub unsafe fn l_Lean_unresolveNameGlobal_x3f___redArg___boxed(
    mut v_inst_7156_: *mut leanh::LeanObject,
    mut v_inst_7157_: *mut leanh::LeanObject,
    mut v_inst_7158_: *mut leanh::LeanObject,
    mut v_inst_7159_: *mut leanh::LeanObject,
    mut v_inst_7160_: *mut leanh::LeanObject,
    mut v_inst_7161_: *mut leanh::LeanObject,
    mut v_n_u2080_7162_: *mut leanh::LeanObject,
    mut v_fullNames_7163_: *mut leanh::LeanObject,
    mut v_allowHorizAliases_7164_: *mut leanh::LeanObject,
    mut v_filter_7165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fullNames_boxed_7166_: u8 = 0;
    let mut v_allowHorizAliases_boxed_7167_: u8 = 0;
    let mut v_res_7168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fullNames_boxed_7166_ = (leanh::lean_unbox(v_fullNames_7163_) as u8);
    v_allowHorizAliases_boxed_7167_ = (leanh::lean_unbox(v_allowHorizAliases_7164_) as u8);
    v_res_7168_ = l_Lean_unresolveNameGlobal_x3f___redArg(
        v_inst_7156_,
        v_inst_7157_,
        v_inst_7158_,
        v_inst_7159_,
        v_inst_7160_,
        v_inst_7161_,
        v_n_u2080_7162_,
        v_fullNames_boxed_7166_,
        v_allowHorizAliases_boxed_7167_,
        v_filter_7165_,
    );
    return v_res_7168_;
}
pub unsafe fn l_Lean_unresolveNameGlobal_x3f(
    mut v_m_7169_: *mut leanh::LeanObject,
    mut v_inst_7170_: *mut leanh::LeanObject,
    mut v_inst_7171_: *mut leanh::LeanObject,
    mut v_inst_7172_: *mut leanh::LeanObject,
    mut v_inst_7173_: *mut leanh::LeanObject,
    mut v_inst_7174_: *mut leanh::LeanObject,
    mut v_inst_7175_: *mut leanh::LeanObject,
    mut v_n_u2080_7176_: *mut leanh::LeanObject,
    mut v_fullNames_7177_: u8,
    mut v_allowHorizAliases_7178_: u8,
    mut v_filter_7179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7180_ = l_Lean_unresolveNameGlobal_x3f___redArg(
        v_inst_7170_,
        v_inst_7171_,
        v_inst_7172_,
        v_inst_7173_,
        v_inst_7174_,
        v_inst_7175_,
        v_n_u2080_7176_,
        v_fullNames_7177_,
        v_allowHorizAliases_7178_,
        v_filter_7179_,
    );
    return v___x_7180_;
}
pub unsafe fn l_Lean_unresolveNameGlobal_x3f___boxed(
    mut v_m_7181_: *mut leanh::LeanObject,
    mut v_inst_7182_: *mut leanh::LeanObject,
    mut v_inst_7183_: *mut leanh::LeanObject,
    mut v_inst_7184_: *mut leanh::LeanObject,
    mut v_inst_7185_: *mut leanh::LeanObject,
    mut v_inst_7186_: *mut leanh::LeanObject,
    mut v_inst_7187_: *mut leanh::LeanObject,
    mut v_n_u2080_7188_: *mut leanh::LeanObject,
    mut v_fullNames_7189_: *mut leanh::LeanObject,
    mut v_allowHorizAliases_7190_: *mut leanh::LeanObject,
    mut v_filter_7191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fullNames_boxed_7192_: u8 = 0;
    let mut v_allowHorizAliases_boxed_7193_: u8 = 0;
    let mut v_res_7194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fullNames_boxed_7192_ = (leanh::lean_unbox(v_fullNames_7189_) as u8);
    v_allowHorizAliases_boxed_7193_ = (leanh::lean_unbox(v_allowHorizAliases_7190_) as u8);
    v_res_7194_ = l_Lean_unresolveNameGlobal_x3f(
        v_m_7181_,
        v_inst_7182_,
        v_inst_7183_,
        v_inst_7184_,
        v_inst_7185_,
        v_inst_7186_,
        v_inst_7187_,
        v_n_u2080_7188_,
        v_fullNames_boxed_7192_,
        v_allowHorizAliases_boxed_7193_,
        v_filter_7191_,
    );
    return v_res_7194_;
}
pub unsafe fn l_Lean_unresolveNameGlobal___redArg___lam__0(
    mut v_toPure_7195_: *mut leanh::LeanObject,
    mut v_n_u2080_7196_: *mut leanh::LeanObject,
    mut v_n_x3f_7197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_n_x3f_7197_) == 0 {
        let mut v___x_7198_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_7198_ =
            leanh::lean_apply_2(v_toPure_7195_, leanh::lean_box(0), v_n_u2080_7196_);
        return v___x_7198_;
    } else {
        let mut v_val_7199_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7200_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_n_u2080_7196_);
        v_val_7199_ = leanh::lean_ctor_get(v_n_x3f_7197_, 0);
        leanh::lean_inc(v_val_7199_);
        leanh::lean_dec_ref_known(v_n_x3f_7197_, 1);
        v___x_7200_ =
            leanh::lean_apply_2(v_toPure_7195_, leanh::lean_box(0), v_val_7199_);
        return v___x_7200_;
    }
}
pub unsafe fn l_Lean_unresolveNameGlobal___redArg(
    mut v_inst_7201_: *mut leanh::LeanObject,
    mut v_inst_7202_: *mut leanh::LeanObject,
    mut v_inst_7203_: *mut leanh::LeanObject,
    mut v_inst_7204_: *mut leanh::LeanObject,
    mut v_inst_7205_: *mut leanh::LeanObject,
    mut v_inst_7206_: *mut leanh::LeanObject,
    mut v_n_u2080_7207_: *mut leanh::LeanObject,
    mut v_fullNames_7208_: u8,
    mut v_allowHorizAliases_7209_: u8,
    mut v_filter_7210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_7211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7211_ = leanh::lean_ctor_get(v_inst_7201_, 0);
    v_toBind_7212_ = leanh::lean_ctor_get(v_inst_7201_, 1);
    leanh::lean_inc(v_toBind_7212_);
    v_toPure_7213_ = leanh::lean_ctor_get(v_toApplicative_7211_, 1);
    leanh::lean_inc(v_toPure_7213_);
    leanh::lean_inc(v_n_u2080_7207_);
    v___x_7214_ = l_Lean_unresolveNameGlobal_x3f___redArg(
        v_inst_7201_,
        v_inst_7202_,
        v_inst_7203_,
        v_inst_7204_,
        v_inst_7205_,
        v_inst_7206_,
        v_n_u2080_7207_,
        v_fullNames_7208_,
        v_allowHorizAliases_7209_,
        v_filter_7210_,
    );
    v___f_7215_ = leanh::lean_alloc_closure(
        l_Lean_unresolveNameGlobal___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_7215_, 0, v_toPure_7213_);
    leanh::lean_closure_set(v___f_7215_, 1, v_n_u2080_7207_);
    v___x_7216_ = leanh::lean_apply_4(
        v_toBind_7212_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_7214_,
        v___f_7215_,
    );
    return v___x_7216_;
}
pub unsafe fn l_Lean_unresolveNameGlobal___redArg___boxed(
    mut v_inst_7217_: *mut leanh::LeanObject,
    mut v_inst_7218_: *mut leanh::LeanObject,
    mut v_inst_7219_: *mut leanh::LeanObject,
    mut v_inst_7220_: *mut leanh::LeanObject,
    mut v_inst_7221_: *mut leanh::LeanObject,
    mut v_inst_7222_: *mut leanh::LeanObject,
    mut v_n_u2080_7223_: *mut leanh::LeanObject,
    mut v_fullNames_7224_: *mut leanh::LeanObject,
    mut v_allowHorizAliases_7225_: *mut leanh::LeanObject,
    mut v_filter_7226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fullNames_boxed_7227_: u8 = 0;
    let mut v_allowHorizAliases_boxed_7228_: u8 = 0;
    let mut v_res_7229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fullNames_boxed_7227_ = (leanh::lean_unbox(v_fullNames_7224_) as u8);
    v_allowHorizAliases_boxed_7228_ = (leanh::lean_unbox(v_allowHorizAliases_7225_) as u8);
    v_res_7229_ = l_Lean_unresolveNameGlobal___redArg(
        v_inst_7217_,
        v_inst_7218_,
        v_inst_7219_,
        v_inst_7220_,
        v_inst_7221_,
        v_inst_7222_,
        v_n_u2080_7223_,
        v_fullNames_boxed_7227_,
        v_allowHorizAliases_boxed_7228_,
        v_filter_7226_,
    );
    return v_res_7229_;
}
pub unsafe fn l_Lean_unresolveNameGlobal(
    mut v_m_7230_: *mut leanh::LeanObject,
    mut v_inst_7231_: *mut leanh::LeanObject,
    mut v_inst_7232_: *mut leanh::LeanObject,
    mut v_inst_7233_: *mut leanh::LeanObject,
    mut v_inst_7234_: *mut leanh::LeanObject,
    mut v_inst_7235_: *mut leanh::LeanObject,
    mut v_inst_7236_: *mut leanh::LeanObject,
    mut v_n_u2080_7237_: *mut leanh::LeanObject,
    mut v_fullNames_7238_: u8,
    mut v_allowHorizAliases_7239_: u8,
    mut v_filter_7240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7241_ = l_Lean_unresolveNameGlobal___redArg(
        v_inst_7231_,
        v_inst_7232_,
        v_inst_7233_,
        v_inst_7234_,
        v_inst_7235_,
        v_inst_7236_,
        v_n_u2080_7237_,
        v_fullNames_7238_,
        v_allowHorizAliases_7239_,
        v_filter_7240_,
    );
    return v___x_7241_;
}
pub unsafe fn l_Lean_unresolveNameGlobal___boxed(
    mut v_m_7242_: *mut leanh::LeanObject,
    mut v_inst_7243_: *mut leanh::LeanObject,
    mut v_inst_7244_: *mut leanh::LeanObject,
    mut v_inst_7245_: *mut leanh::LeanObject,
    mut v_inst_7246_: *mut leanh::LeanObject,
    mut v_inst_7247_: *mut leanh::LeanObject,
    mut v_inst_7248_: *mut leanh::LeanObject,
    mut v_n_u2080_7249_: *mut leanh::LeanObject,
    mut v_fullNames_7250_: *mut leanh::LeanObject,
    mut v_allowHorizAliases_7251_: *mut leanh::LeanObject,
    mut v_filter_7252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fullNames_boxed_7253_: u8 = 0;
    let mut v_allowHorizAliases_boxed_7254_: u8 = 0;
    let mut v_res_7255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fullNames_boxed_7253_ = (leanh::lean_unbox(v_fullNames_7250_) as u8);
    v_allowHorizAliases_boxed_7254_ = (leanh::lean_unbox(v_allowHorizAliases_7251_) as u8);
    v_res_7255_ = l_Lean_unresolveNameGlobal(
        v_m_7242_,
        v_inst_7243_,
        v_inst_7244_,
        v_inst_7245_,
        v_inst_7246_,
        v_inst_7247_,
        v_inst_7248_,
        v_n_u2080_7249_,
        v_fullNames_boxed_7253_,
        v_allowHorizAliases_boxed_7254_,
        v_filter_7252_,
    );
    return v_res_7255_;
}
pub unsafe fn l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0(
    mut v_toFunctor_7257_: *mut leanh::LeanObject,
    mut v_inst_7258_: *mut leanh::LeanObject,
    mut v_inst_7259_: *mut leanh::LeanObject,
    mut v_inst_7260_: *mut leanh::LeanObject,
    mut v_inst_7261_: *mut leanh::LeanObject,
    mut v_inst_7262_: *mut leanh::LeanObject,
    mut v_inst_7263_: *mut leanh::LeanObject,
    mut v_inst_7264_: *mut leanh::LeanObject,
    mut v_n_7265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_7266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_7266_ = leanh::lean_ctor_get(v_toFunctor_7257_, 0);
    leanh::lean_inc(v_map_7266_);
    leanh::lean_dec_ref(v_toFunctor_7257_);
    v___x_7267_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0___closed__0;
    v___x_7268_ = l_Lean_resolveLocalName___redArg(
        v_inst_7258_,
        v_inst_7259_,
        v_inst_7260_,
        v_inst_7261_,
        v_inst_7262_,
        v_inst_7263_,
        v_inst_7264_,
        v_n_7265_,
    );
    v___x_7269_ = leanh::lean_apply_4(
        v_map_7266_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_7267_,
        v___x_7268_,
    );
    return v___x_7269_;
}
pub unsafe fn l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(
    mut v_inst_7270_: *mut leanh::LeanObject,
    mut v_inst_7271_: *mut leanh::LeanObject,
    mut v_inst_7272_: *mut leanh::LeanObject,
    mut v_inst_7273_: *mut leanh::LeanObject,
    mut v_inst_7274_: *mut leanh::LeanObject,
    mut v_inst_7275_: *mut leanh::LeanObject,
    mut v_inst_7276_: *mut leanh::LeanObject,
    mut v_n_u2080_7277_: *mut leanh::LeanObject,
    mut v_fullNames_7278_: u8,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_7279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_7280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7281_: u8 = 0;
    let mut v___f_7282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7279_ = leanh::lean_ctor_get(v_inst_7270_, 0);
    v_toFunctor_7280_ = leanh::lean_ctor_get(v_toApplicative_7279_, 0);
    v___x_7281_ = 0;
    leanh::lean_inc(v_inst_7275_);
    leanh::lean_inc_ref(v_inst_7274_);
    leanh::lean_inc(v_inst_7273_);
    leanh::lean_inc_ref(v_inst_7272_);
    leanh::lean_inc_ref(v_inst_7271_);
    leanh::lean_inc_ref(v_inst_7270_);
    leanh::lean_inc_ref(v_toFunctor_7280_);
    v___f_7282_ = leanh::lean_alloc_closure(
        l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_7282_, 0, v_toFunctor_7280_);
    leanh::lean_closure_set(v___f_7282_, 1, v_inst_7270_);
    leanh::lean_closure_set(v___f_7282_, 2, v_inst_7271_);
    leanh::lean_closure_set(v___f_7282_, 3, v_inst_7272_);
    leanh::lean_closure_set(v___f_7282_, 4, v_inst_7273_);
    leanh::lean_closure_set(v___f_7282_, 5, v_inst_7274_);
    leanh::lean_closure_set(v___f_7282_, 6, v_inst_7275_);
    leanh::lean_closure_set(v___f_7282_, 7, v_inst_7276_);
    v___x_7283_ = l_Lean_unresolveNameGlobal_x3f___redArg(
        v_inst_7270_,
        v_inst_7271_,
        v_inst_7272_,
        v_inst_7273_,
        v_inst_7274_,
        v_inst_7275_,
        v_n_u2080_7277_,
        v_fullNames_7278_,
        v___x_7281_,
        v___f_7282_,
    );
    return v___x_7283_;
}
pub unsafe fn l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___boxed(
    mut v_inst_7284_: *mut leanh::LeanObject,
    mut v_inst_7285_: *mut leanh::LeanObject,
    mut v_inst_7286_: *mut leanh::LeanObject,
    mut v_inst_7287_: *mut leanh::LeanObject,
    mut v_inst_7288_: *mut leanh::LeanObject,
    mut v_inst_7289_: *mut leanh::LeanObject,
    mut v_inst_7290_: *mut leanh::LeanObject,
    mut v_n_u2080_7291_: *mut leanh::LeanObject,
    mut v_fullNames_7292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fullNames_boxed_7293_: u8 = 0;
    let mut v_res_7294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fullNames_boxed_7293_ = (leanh::lean_unbox(v_fullNames_7292_) as u8);
    v_res_7294_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(
        v_inst_7284_,
        v_inst_7285_,
        v_inst_7286_,
        v_inst_7287_,
        v_inst_7288_,
        v_inst_7289_,
        v_inst_7290_,
        v_n_u2080_7291_,
        v_fullNames_boxed_7293_,
    );
    return v_res_7294_;
}
pub unsafe fn l_Lean_unresolveNameGlobalAvoidingLocals_x3f(
    mut v_m_7295_: *mut leanh::LeanObject,
    mut v_inst_7296_: *mut leanh::LeanObject,
    mut v_inst_7297_: *mut leanh::LeanObject,
    mut v_inst_7298_: *mut leanh::LeanObject,
    mut v_inst_7299_: *mut leanh::LeanObject,
    mut v_inst_7300_: *mut leanh::LeanObject,
    mut v_inst_7301_: *mut leanh::LeanObject,
    mut v_inst_7302_: *mut leanh::LeanObject,
    mut v_n_u2080_7303_: *mut leanh::LeanObject,
    mut v_fullNames_7304_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_7305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7305_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(
        v_inst_7296_,
        v_inst_7297_,
        v_inst_7298_,
        v_inst_7299_,
        v_inst_7300_,
        v_inst_7301_,
        v_inst_7302_,
        v_n_u2080_7303_,
        v_fullNames_7304_,
    );
    return v___x_7305_;
}
pub unsafe fn l_Lean_unresolveNameGlobalAvoidingLocals_x3f___boxed(
    mut v_m_7306_: *mut leanh::LeanObject,
    mut v_inst_7307_: *mut leanh::LeanObject,
    mut v_inst_7308_: *mut leanh::LeanObject,
    mut v_inst_7309_: *mut leanh::LeanObject,
    mut v_inst_7310_: *mut leanh::LeanObject,
    mut v_inst_7311_: *mut leanh::LeanObject,
    mut v_inst_7312_: *mut leanh::LeanObject,
    mut v_inst_7313_: *mut leanh::LeanObject,
    mut v_n_u2080_7314_: *mut leanh::LeanObject,
    mut v_fullNames_7315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fullNames_boxed_7316_: u8 = 0;
    let mut v_res_7317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fullNames_boxed_7316_ = (leanh::lean_unbox(v_fullNames_7315_) as u8);
    v_res_7317_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f(
        v_m_7306_,
        v_inst_7307_,
        v_inst_7308_,
        v_inst_7309_,
        v_inst_7310_,
        v_inst_7311_,
        v_inst_7312_,
        v_inst_7313_,
        v_n_u2080_7314_,
        v_fullNames_boxed_7316_,
    );
    return v_res_7317_;
}
pub unsafe fn l_Lean_unresolveNameGlobalAvoidingLocals___redArg(
    mut v_inst_7318_: *mut leanh::LeanObject,
    mut v_inst_7319_: *mut leanh::LeanObject,
    mut v_inst_7320_: *mut leanh::LeanObject,
    mut v_inst_7321_: *mut leanh::LeanObject,
    mut v_inst_7322_: *mut leanh::LeanObject,
    mut v_inst_7323_: *mut leanh::LeanObject,
    mut v_inst_7324_: *mut leanh::LeanObject,
    mut v_n_u2080_7325_: *mut leanh::LeanObject,
    mut v_fullNames_7326_: u8,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_7327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7327_ = leanh::lean_ctor_get(v_inst_7318_, 0);
    v_toBind_7328_ = leanh::lean_ctor_get(v_inst_7318_, 1);
    leanh::lean_inc(v_toBind_7328_);
    v_toPure_7329_ = leanh::lean_ctor_get(v_toApplicative_7327_, 1);
    leanh::lean_inc(v_toPure_7329_);
    leanh::lean_inc(v_n_u2080_7325_);
    v___x_7330_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(
        v_inst_7318_,
        v_inst_7319_,
        v_inst_7320_,
        v_inst_7321_,
        v_inst_7322_,
        v_inst_7323_,
        v_inst_7324_,
        v_n_u2080_7325_,
        v_fullNames_7326_,
    );
    v___f_7331_ = leanh::lean_alloc_closure(
        l_Lean_unresolveNameGlobal___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_7331_, 0, v_toPure_7329_);
    leanh::lean_closure_set(v___f_7331_, 1, v_n_u2080_7325_);
    v___x_7332_ = leanh::lean_apply_4(
        v_toBind_7328_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_7330_,
        v___f_7331_,
    );
    return v___x_7332_;
}
pub unsafe fn l_Lean_unresolveNameGlobalAvoidingLocals___redArg___boxed(
    mut v_inst_7333_: *mut leanh::LeanObject,
    mut v_inst_7334_: *mut leanh::LeanObject,
    mut v_inst_7335_: *mut leanh::LeanObject,
    mut v_inst_7336_: *mut leanh::LeanObject,
    mut v_inst_7337_: *mut leanh::LeanObject,
    mut v_inst_7338_: *mut leanh::LeanObject,
    mut v_inst_7339_: *mut leanh::LeanObject,
    mut v_n_u2080_7340_: *mut leanh::LeanObject,
    mut v_fullNames_7341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fullNames_boxed_7342_: u8 = 0;
    let mut v_res_7343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fullNames_boxed_7342_ = (leanh::lean_unbox(v_fullNames_7341_) as u8);
    v_res_7343_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(
        v_inst_7333_,
        v_inst_7334_,
        v_inst_7335_,
        v_inst_7336_,
        v_inst_7337_,
        v_inst_7338_,
        v_inst_7339_,
        v_n_u2080_7340_,
        v_fullNames_boxed_7342_,
    );
    return v_res_7343_;
}
pub unsafe fn l_Lean_unresolveNameGlobalAvoidingLocals(
    mut v_m_7344_: *mut leanh::LeanObject,
    mut v_inst_7345_: *mut leanh::LeanObject,
    mut v_inst_7346_: *mut leanh::LeanObject,
    mut v_inst_7347_: *mut leanh::LeanObject,
    mut v_inst_7348_: *mut leanh::LeanObject,
    mut v_inst_7349_: *mut leanh::LeanObject,
    mut v_inst_7350_: *mut leanh::LeanObject,
    mut v_inst_7351_: *mut leanh::LeanObject,
    mut v_n_u2080_7352_: *mut leanh::LeanObject,
    mut v_fullNames_7353_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_7354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7354_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(
        v_inst_7345_,
        v_inst_7346_,
        v_inst_7347_,
        v_inst_7348_,
        v_inst_7349_,
        v_inst_7350_,
        v_inst_7351_,
        v_n_u2080_7352_,
        v_fullNames_7353_,
    );
    return v___x_7354_;
}
pub unsafe fn l_Lean_unresolveNameGlobalAvoidingLocals___boxed(
    mut v_m_7355_: *mut leanh::LeanObject,
    mut v_inst_7356_: *mut leanh::LeanObject,
    mut v_inst_7357_: *mut leanh::LeanObject,
    mut v_inst_7358_: *mut leanh::LeanObject,
    mut v_inst_7359_: *mut leanh::LeanObject,
    mut v_inst_7360_: *mut leanh::LeanObject,
    mut v_inst_7361_: *mut leanh::LeanObject,
    mut v_inst_7362_: *mut leanh::LeanObject,
    mut v_n_u2080_7363_: *mut leanh::LeanObject,
    mut v_fullNames_7364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fullNames_boxed_7365_: u8 = 0;
    let mut v_res_7366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fullNames_boxed_7365_ = (leanh::lean_unbox(v_fullNames_7364_) as u8);
    v_res_7366_ = l_Lean_unresolveNameGlobalAvoidingLocals(
        v_m_7355_,
        v_inst_7356_,
        v_inst_7357_,
        v_inst_7358_,
        v_inst_7359_,
        v_inst_7360_,
        v_inst_7361_,
        v_inst_7362_,
        v_n_u2080_7363_,
        v_fullNames_boxed_7365_,
    );
    return v_res_7366_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_ResolveName(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Modifiers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Exception(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Namespace(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Log(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_reservedNamePredicatesRef = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_reservedNamePredicatesRef);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_reservedNamePredicatesExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_reservedNamePredicatesExt);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_aliasExtension = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_aliasExtension);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_ResolveName_backward_privateInPublic = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_ResolveName_backward_privateInPublic);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_ResolveName_backward_privateInPublic_warn = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_ResolveName_backward_privateInPublic_warn);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_ResolveName(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_ResolveName(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Modifiers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Exception(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Namespace(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Log(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ResolveName(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_ResolveName(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_ResolveName(builtin);
}
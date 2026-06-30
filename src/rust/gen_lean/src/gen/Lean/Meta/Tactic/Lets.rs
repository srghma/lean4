// Lean compiler output
// Module: Lean.Meta.Tactic.Lets
// Imports: Lean.Meta.Tactic.Replace Lean.Meta.LetToHave
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_set, lean_array_size,
    lean_array_to_list, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_expr_abstract, lean_expr_eqv, lean_expr_instantiate1, lean_find_expr, lean_infer_type,
    lean_mk_array, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_ptr_addr, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_mix_hash, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le, lean_usize_dec_lt,
    lean_usize_land, lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Core::l_instBEqProd___redArg___lam__0___boxed;
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Hashable::{
    l_instHashableBool___lam__0___boxed, l_instHashableProd___redArg___lam__0___boxed,
};
use crate::r#gen::Init::Data::List::Basic::l_List_isEmpty___redArg;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_hasMacroScopes, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instBEqOfDecidableEq___redArg___lam__0___boxed,
    l_instInhabitedForall___redArg___lam__0___boxed, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Core_mkFreshUserName,
};
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_isAnonymous,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_instInhabitedPersistentArrayNode_default;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_BinderInfo_isExplicit,
    l_Lean_Expr_forallE___override, l_Lean_Expr_fvar___override, l_Lean_Expr_fvarId_x21,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasFVar,
    l_Lean_Expr_hasLooseBVars, l_Lean_Expr_hasMVar, l_Lean_Expr_isAtomic, l_Lean_Expr_isLet,
    l_Lean_Expr_isLet___boxed, l_Lean_Expr_isMData, l_Lean_Expr_lam___override,
    l_Lean_Expr_letE___override, l_Lean_Expr_mdata___override, l_Lean_Expr_mvarId_x21,
    l_Lean_Expr_proj___override, l_Lean_Expr_sort___override, l_Lean_ExprStructEq_beq,
    l_Lean_ExprStructEq_beq___boxed, l_Lean_ExprStructEq_hash, l_Lean_ExprStructEq_hash___boxed,
    l_Lean_FVarIdSet_insert, l_Lean_instBEqBinderInfo_beq, l_Lean_instBEqFVarId_beq,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_instInhabitedExpr,
    l_Lean_mkAppN,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_contains, l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_isImplementationDetail,
    l_Lean_LocalDecl_isLet, l_Lean_LocalDecl_toExpr, l_Lean_LocalDecl_type,
    l_Lean_LocalDecl_userName, l_Lean_LocalDecl_value,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getDecl___redArg,
    l_Lean_FVarId_getType___redArg, l_Lean_Meta_instInhabitedExprParamInfo_default,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    l_Lean_Meta_instantiateForallWithParamInfos, l_Lean_Meta_mkLetFVars,
    l_Lean_Meta_withExistingLocalDecls___redArg,
};
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_isProof, l_Lean_Meta_isType};
use crate::r#gen::Lean::Meta::LetToHave::{
    initialize_Lean_Meta_LetToHave, l_Lean_Meta_letToHave, runtime_initialize_Lean_Meta_LetToHave,
};
use crate::r#gen::Lean::Meta::Tactic::Replace::{
    initialize_Lean_Meta_Tactic_Replace, l_Lean_MVarId_replaceLocalDeclDefEq,
    l_Lean_MVarId_replaceTargetDefEq, l_Lean_MVarId_withReverted___redArg,
    runtime_initialize_Lean_Meta_Tactic_Replace,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getTag, l_Lean_MVarId_getType,
    l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar, l_Lean_Meta_throwTacticEx___redArg,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::MonadCache::l_Lean_MonadCacheT_instMonad___redArg;
pub static l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0_value:
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
static mut l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_ExtractLets_instInhabitedState_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_ExtractLets_instInhabitedState: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__0_value:
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
    m_data: [95, 0],
};
static mut l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        13286986945483979944 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___closed__0_value:
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
    m_data: [97, 0],
};
static mut l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___closed__0_value
        ) as *mut leanh::LeanObject,
        7839396180116328695 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_ExtractLets_flushDecls___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0_value
            ) as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0_value
            ) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_ExtractLets_flushDecls___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ExtractLets_flushDecls___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__6_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__7_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__0_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__1_value) as *mut leanh::LeanObject] };
static mut l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__8_value: leanh::LeanCtorObject<5> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__4_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__5_value) as *mut leanh::LeanObject] };
static mut l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__6_value) as *mut leanh::LeanObject] };
static mut l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___closed__0_value:
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
    m_fun: l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_ExtractLets_containsLet___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Expr_isLet___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_ExtractLets_containsLet___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ExtractLets_containsLet___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3_value:
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
    m_fun: l_Lean_ExprStructEq_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4_value:
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
    m_fun: l_instHashableBool___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__5_value:
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
    m_fun: l_Lean_ExprStructEq_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__5_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__6_value:
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
    m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__6_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__7_value:
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
    m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__7_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__2_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [108, 101, 116, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__1_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 117, 112, 100, 97, 116, 101, 76, 101, 116, 69, 33, 0]};
static mut l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [76, 101, 97, 110, 46, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__3_value:
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
static mut l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__2_value:
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
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 69, 120, 116, 114, 97, 99, 116, 76, 101, 116,
        115, 46, 101, 120, 116, 114, 97, 99, 116, 67, 111, 114, 101, 0,
    ],
};
static mut l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__1_value:
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
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 76, 101, 116,
        115, 0,
    ],
};
static mut l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_liftLets___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_liftLets___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__0_value:
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
        109, 97, 100, 101, 32, 110, 111, 32, 112, 114, 111, 103, 114, 101, 115, 115, 0,
    ],
};
static mut l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_extractLets___closed__0_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [101, 120, 116, 114, 97, 99, 116, 95, 108, 101, 116, 115, 0],
    };
static mut l_Lean_MVarId_extractLets___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_extractLets___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_extractLets___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_extractLets___closed__0_value)
                as *mut leanh::LeanObject,
            4644032510077903208 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_extractLets___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_extractLets___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__0_value:
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
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 117, 120, 105, 108, 105, 97, 114,
        121, 32, 116, 97, 114, 103, 101, 116, 0,
    ],
};
static mut l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_liftLets___closed__0_value: leanh::LeanStringObject<10> =
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
        m_data: [108, 105, 102, 116, 95, 108, 101, 116, 115, 0],
    };
static mut l_Lean_MVarId_liftLets___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_liftLets___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_MVarId_liftLets___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_liftLets___closed__0_value)
                as *mut leanh::LeanObject,
            7326091052943921366 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_liftLets___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_liftLets___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_MVarId_letToHave___closed__0_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [108, 101, 116, 95, 116, 111, 95, 104, 97, 118, 101, 0],
    };
static mut l_Lean_MVarId_letToHave___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_letToHave___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_MVarId_letToHave___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_letToHave___closed__0_value)
                as *mut leanh::LeanObject,
            6130153969274943757 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_letToHave___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_letToHave___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5088_ = leanh::lean_box(0);
    v___x_5089_ = leanh::lean_unsigned_to_nat(16);
    v___x_5090_ = lean_mk_array(v___x_5089_, v___x_5088_);
    return v___x_5090_;
}
pub unsafe fn _init_l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5091_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__1_once
        ),
        _init_l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__1,
    );
    v___x_5092_ = leanh::lean_unsigned_to_nat(0);
    v___x_5093_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5093_, 0, v___x_5092_);
    leanh::lean_ctor_set(v___x_5093_, 1, v___x_5091_);
    return v___x_5093_;
}
pub unsafe fn _init_l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5094_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__2_once
        ),
        _init_l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__2,
    );
    v___x_5095_ = l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0;
    v___x_5096_ = leanh::lean_box(0);
    v___x_5097_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_5097_, 0, v___x_5096_);
    leanh::lean_ctor_set(v___x_5097_, 1, v___x_5095_);
    leanh::lean_ctor_set(v___x_5097_, 2, v___x_5094_);
    return v___x_5097_;
}
pub unsafe fn _init_l_Lean_Meta_ExtractLets_instInhabitedState_default()
-> *mut leanh::LeanObject {
    let mut v___x_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5098_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__3_once
        ),
        _init_l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__3,
    );
    return v___x_5098_;
}
pub unsafe fn _init_l_Lean_Meta_ExtractLets_instInhabitedState() -> *mut leanh::LeanObject {
    let mut v___x_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5099_ = l_Lean_Meta_ExtractLets_instInhabitedState_default;
    return v___x_5099_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_hasNextName___redArg(
    mut v_a_5100_: *mut leanh::LeanObject,
    mut v_a_5101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_onlyGivenNames_5104_: u8 = 0;
    v___x_5103_ = lean_st_ref_get(v_a_5101_);
    v_onlyGivenNames_5104_ = leanh::lean_ctor_get_uint8(v_a_5100_, 8 as u32);
    if v_onlyGivenNames_5104_ == 0 {
        let mut v___x_5105_: u8 = 0;
        let mut v___x_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_5103_);
        v___x_5105_ = 1;
        v___x_5106_ = leanh::lean_box((v___x_5105_) as usize);
        v___x_5107_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5107_, 0, v___x_5106_);
        return v___x_5107_;
    } else {
        let mut v_givenNames_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5109_: u8 = 0;
        v_givenNames_5108_ = leanh::lean_ctor_get(v___x_5103_, 0);
        leanh::lean_inc(v_givenNames_5108_);
        leanh::lean_dec(v___x_5103_);
        v___x_5109_ = l_List_isEmpty___redArg(v_givenNames_5108_);
        leanh::lean_dec(v_givenNames_5108_);
        if v___x_5109_ == 0 {
            let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5110_ = leanh::lean_box((v_onlyGivenNames_5104_) as usize);
            v___x_5111_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_5111_, 0, v___x_5110_);
            return v___x_5111_;
        } else {
            let mut v___x_5112_: u8 = 0;
            let mut v___x_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5112_ = 0;
            v___x_5113_ = leanh::lean_box((v___x_5112_) as usize);
            v___x_5114_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_5114_, 0, v___x_5113_);
            return v___x_5114_;
        }
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_hasNextName___redArg___boxed(
    mut v_a_5115_: *mut leanh::LeanObject,
    mut v_a_5116_: *mut leanh::LeanObject,
    mut v_a_5117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5118_ = l_Lean_Meta_ExtractLets_hasNextName___redArg(v_a_5115_, v_a_5116_);
    leanh::lean_dec(v_a_5116_);
    leanh::lean_dec_ref(v_a_5115_);
    return v_res_5118_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_hasNextName(
    mut v_a_5119_: *mut leanh::LeanObject,
    mut v_a_5120_: *mut leanh::LeanObject,
    mut v_a_5121_: *mut leanh::LeanObject,
    mut v_a_5122_: *mut leanh::LeanObject,
    mut v_a_5123_: *mut leanh::LeanObject,
    mut v_a_5124_: *mut leanh::LeanObject,
    mut v_a_5125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5127_ = l_Lean_Meta_ExtractLets_hasNextName___redArg(v_a_5119_, v_a_5121_);
    return v___x_5127_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_hasNextName___boxed(
    mut v_a_5128_: *mut leanh::LeanObject,
    mut v_a_5129_: *mut leanh::LeanObject,
    mut v_a_5130_: *mut leanh::LeanObject,
    mut v_a_5131_: *mut leanh::LeanObject,
    mut v_a_5132_: *mut leanh::LeanObject,
    mut v_a_5133_: *mut leanh::LeanObject,
    mut v_a_5134_: *mut leanh::LeanObject,
    mut v_a_5135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5136_ = l_Lean_Meta_ExtractLets_hasNextName(
        v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_,
    );
    leanh::lean_dec(v_a_5134_);
    leanh::lean_dec_ref(v_a_5133_);
    leanh::lean_dec(v_a_5132_);
    leanh::lean_dec_ref(v_a_5131_);
    leanh::lean_dec(v_a_5130_);
    leanh::lean_dec(v_a_5129_);
    leanh::lean_dec_ref(v_a_5128_);
    return v_res_5136_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_nextName_x3f___redArg(
    mut v_a_5142_: *mut leanh::LeanObject,
    mut v_a_5143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_givenNames_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_onlyGivenNames_5147_: u8 = 0;
    let mut v___x_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_valueMap_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5156_: u8 = 0;
    let mut v_head_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5165_: u8 = 0;
    let mut v_unused_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5145_ = lean_st_ref_get(v_a_5143_);
                v_givenNames_5146_ = leanh::lean_ctor_get(v___x_5145_, 0);
                leanh::lean_inc(v_givenNames_5146_);
                if leanh::lean_obj_tag(v_givenNames_5146_) == 0 {
                    leanh::lean_dec(v___x_5145_);
                    v_onlyGivenNames_5147_ = leanh::lean_ctor_get_uint8(v_a_5142_, 8 as u32);
                    if v_onlyGivenNames_5147_ == 0 {
                        v___x_5148_ = l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__2;
                        v___x_5149_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5149_, 0, v___x_5148_);
                        return v___x_5149_;
                    } else {
                        v___x_5150_ = leanh::lean_box(0);
                        v___x_5151_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5151_, 0, v___x_5150_);
                        return v___x_5151_;
                    }
                } else {
                    v_decls_5152_ = leanh::lean_ctor_get(v___x_5145_, 1);
                    v_valueMap_5153_ = leanh::lean_ctor_get(v___x_5145_, 2);
                    v_isSharedCheck_5165_ = (!leanh::lean_is_exclusive(v___x_5145_)) as u8;
                    if v_isSharedCheck_5165_ == 0 {
                        v_unused_5166_ = leanh::lean_ctor_get(v___x_5145_, 0);
                        leanh::lean_dec(v_unused_5166_);
                        v___x_5155_ = v___x_5145_;
                        v_isShared_5156_ = v_isSharedCheck_5165_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_valueMap_5153_);
                        leanh::lean_inc(v_decls_5152_);
                        leanh::lean_dec(v___x_5145_);
                        v___x_5155_ = leanh::lean_box(0);
                        v_isShared_5156_ = v_isSharedCheck_5165_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_head_5157_ = leanh::lean_ctor_get(v_givenNames_5146_, 0);
                leanh::lean_inc(v_head_5157_);
                v_tail_5158_ = leanh::lean_ctor_get(v_givenNames_5146_, 1);
                leanh::lean_inc(v_tail_5158_);
                leanh::lean_dec_ref_known(v_givenNames_5146_, 2);
                if v_isShared_5156_ == 0 {
                    leanh::lean_ctor_set(v___x_5155_, 0, v_tail_5158_);
                    v___x_5160_ = v___x_5155_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5164_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5164_, 0, v_tail_5158_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5164_, 1, v_decls_5152_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5164_, 2, v_valueMap_5153_);
                    v___x_5160_ = v_reuseFailAlloc_5164_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5161_ = lean_st_ref_set(v_a_5143_, v___x_5160_);
                v___x_5162_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5162_, 0, v_head_5157_);
                v___x_5163_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5163_, 0, v___x_5162_);
                return v___x_5163_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_nextName_x3f___redArg___boxed(
    mut v_a_5167_: *mut leanh::LeanObject,
    mut v_a_5168_: *mut leanh::LeanObject,
    mut v_a_5169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5170_ = l_Lean_Meta_ExtractLets_nextName_x3f___redArg(v_a_5167_, v_a_5168_);
    leanh::lean_dec(v_a_5168_);
    leanh::lean_dec_ref(v_a_5167_);
    return v_res_5170_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_nextName_x3f(
    mut v_a_5171_: *mut leanh::LeanObject,
    mut v_a_5172_: *mut leanh::LeanObject,
    mut v_a_5173_: *mut leanh::LeanObject,
    mut v_a_5174_: *mut leanh::LeanObject,
    mut v_a_5175_: *mut leanh::LeanObject,
    mut v_a_5176_: *mut leanh::LeanObject,
    mut v_a_5177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5179_ = l_Lean_Meta_ExtractLets_nextName_x3f___redArg(v_a_5171_, v_a_5173_);
    return v___x_5179_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_nextName_x3f___boxed(
    mut v_a_5180_: *mut leanh::LeanObject,
    mut v_a_5181_: *mut leanh::LeanObject,
    mut v_a_5182_: *mut leanh::LeanObject,
    mut v_a_5183_: *mut leanh::LeanObject,
    mut v_a_5184_: *mut leanh::LeanObject,
    mut v_a_5185_: *mut leanh::LeanObject,
    mut v_a_5186_: *mut leanh::LeanObject,
    mut v_a_5187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5188_ = l_Lean_Meta_ExtractLets_nextName_x3f(
        v_a_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_,
    );
    leanh::lean_dec(v_a_5186_);
    leanh::lean_dec_ref(v_a_5185_);
    leanh::lean_dec(v_a_5184_);
    leanh::lean_dec_ref(v_a_5183_);
    leanh::lean_dec(v_a_5182_);
    leanh::lean_dec(v_a_5181_);
    leanh::lean_dec_ref(v_a_5180_);
    return v_res_5188_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(
    mut v_binderName_5192_: *mut leanh::LeanObject,
    mut v_a_5193_: *mut leanh::LeanObject,
    mut v_a_5194_: *mut leanh::LeanObject,
    mut v_a_5195_: *mut leanh::LeanObject,
    mut v_a_5196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5203_: u8 = 0;
    let mut v___x_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: u8 = 0;
    let mut v___x_5206_: u8 = 0;
    let mut v_preserveBinderNames_5207_: u8 = 0;
    let mut v___x_5208_: u8 = 0;
    let mut v___x_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5213_: u8 = 0;
    let mut v___x_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5220_: u8 = 0;
    let mut v_a_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5224_: u8 = 0;
    let mut v___x_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5228_: u8 = 0;
    let mut v___x_5229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5234_: u8 = 0;
    let mut v___x_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5241_: u8 = 0;
    let mut v_a_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5245_: u8 = 0;
    let mut v___x_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5249_: u8 = 0;
    let mut v_isSharedCheck_5250_: u8 = 0;
    let mut v___x_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5253_: u8 = 0;
    let mut v___x_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5258_: u8 = 0;
    let mut v_unused_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5198_ = l_Lean_Meta_ExtractLets_nextName_x3f___redArg(v_a_5193_, v_a_5194_);
                v_a_5199_ = leanh::lean_ctor_get(v___x_5198_, 0);
                leanh::lean_inc(v_a_5199_);
                if leanh::lean_obj_tag(v_a_5199_) == 1 {
                    v_val_5200_ = leanh::lean_ctor_get(v_a_5199_, 0);
                    v_isSharedCheck_5250_ = (!leanh::lean_is_exclusive(v_a_5199_)) as u8;
                    if v_isSharedCheck_5250_ == 0 {
                        v___x_5202_ = v_a_5199_;
                        v_isShared_5203_ = v_isSharedCheck_5250_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5200_);
                        leanh::lean_dec(v_a_5199_);
                        v___x_5202_ = leanh::lean_box(0);
                        v_isShared_5203_ = v_isSharedCheck_5250_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5199_);
                    leanh::lean_dec(v_binderName_5192_);
                    v_isSharedCheck_5258_ = (!leanh::lean_is_exclusive(v___x_5198_)) as u8;
                    if v_isSharedCheck_5258_ == 0 {
                        v_unused_5259_ = leanh::lean_ctor_get(v___x_5198_, 0);
                        leanh::lean_dec(v_unused_5259_);
                        v___x_5252_ = v___x_5198_;
                        v_isShared_5253_ = v_isSharedCheck_5258_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5198_);
                        v___x_5252_ = leanh::lean_box(0);
                        v_isShared_5253_ = v_isSharedCheck_5258_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5204_ = l_Lean_Meta_ExtractLets_nextName_x3f___redArg___closed__1;
                v___x_5205_ = lean_name_eq(v_val_5200_, v___x_5204_);
                if v___x_5205_ == 0 {
                    leanh::lean_del_object(v___x_5202_);
                    leanh::lean_dec(v_val_5200_);
                    leanh::lean_dec(v_binderName_5192_);
                    return v___x_5198_;
                } else {
                    v___x_5206_ = l_Lean_Name_isAnonymous(v_binderName_5192_);
                    if v___x_5206_ == 0 {
                        v_preserveBinderNames_5207_ =
                            leanh::lean_ctor_get_uint8(v_a_5193_, 9 as u32);
                        if v_preserveBinderNames_5207_ == 0 {
                            v___x_5208_ = l_Lean_Name_hasMacroScopes(v_val_5200_);
                            leanh::lean_dec(v_val_5200_);
                            if v___x_5208_ == 0 {
                                leanh::lean_dec_ref(v___x_5198_);
                                v___x_5209_ = l_Lean_Core_mkFreshUserName(
                                    v_binderName_5192_,
                                    v_a_5195_,
                                    v_a_5196_,
                                );
                                if leanh::lean_obj_tag(v___x_5209_) == 0 {
                                    v_a_5210_ = leanh::lean_ctor_get(v___x_5209_, 0);
                                    v_isSharedCheck_5220_ =
                                        (!leanh::lean_is_exclusive(v___x_5209_)) as u8;
                                    if v_isSharedCheck_5220_ == 0 {
                                        v___x_5212_ = v___x_5209_;
                                        v_isShared_5213_ = v_isSharedCheck_5220_;
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5210_);
                                        leanh::lean_dec(v___x_5209_);
                                        v___x_5212_ = leanh::lean_box(0);
                                        v_isShared_5213_ = v_isSharedCheck_5220_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_del_object(v___x_5202_);
                                    v_a_5221_ = leanh::lean_ctor_get(v___x_5209_, 0);
                                    v_isSharedCheck_5228_ =
                                        (!leanh::lean_is_exclusive(v___x_5209_)) as u8;
                                    if v_isSharedCheck_5228_ == 0 {
                                        v___x_5223_ = v___x_5209_;
                                        v_isShared_5224_ = v_isSharedCheck_5228_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5221_);
                                        leanh::lean_dec(v___x_5209_);
                                        v___x_5223_ = leanh::lean_box(0);
                                        v_isShared_5224_ = v_isSharedCheck_5228_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_del_object(v___x_5202_);
                                leanh::lean_dec(v_binderName_5192_);
                                return v___x_5198_;
                            }
                        } else {
                            leanh::lean_del_object(v___x_5202_);
                            leanh::lean_dec(v_val_5200_);
                            leanh::lean_dec(v_binderName_5192_);
                            return v___x_5198_;
                        }
                    } else {
                        leanh::lean_dec(v_val_5200_);
                        leanh::lean_dec_ref(v___x_5198_);
                        leanh::lean_dec(v_binderName_5192_);
                        v___x_5229_ =
                            l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___closed__1;
                        v___x_5230_ =
                            l_Lean_Core_mkFreshUserName(v___x_5229_, v_a_5195_, v_a_5196_);
                        if leanh::lean_obj_tag(v___x_5230_) == 0 {
                            v_a_5231_ = leanh::lean_ctor_get(v___x_5230_, 0);
                            v_isSharedCheck_5241_ =
                                (!leanh::lean_is_exclusive(v___x_5230_)) as u8;
                            if v_isSharedCheck_5241_ == 0 {
                                v___x_5233_ = v___x_5230_;
                                v_isShared_5234_ = v_isSharedCheck_5241_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5231_);
                                leanh::lean_dec(v___x_5230_);
                                v___x_5233_ = leanh::lean_box(0);
                                v_isShared_5234_ = v_isSharedCheck_5241_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_5202_);
                            v_a_5242_ = leanh::lean_ctor_get(v___x_5230_, 0);
                            v_isSharedCheck_5249_ =
                                (!leanh::lean_is_exclusive(v___x_5230_)) as u8;
                            if v_isSharedCheck_5249_ == 0 {
                                v___x_5244_ = v___x_5230_;
                                v_isShared_5245_ = v_isSharedCheck_5249_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5242_);
                                leanh::lean_dec(v___x_5230_);
                                v___x_5244_ = leanh::lean_box(0);
                                v_isShared_5245_ = v_isSharedCheck_5249_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                if v_isShared_5203_ == 0 {
                    leanh::lean_ctor_set(v___x_5202_, 0, v_a_5210_);
                    v___x_5215_ = v___x_5202_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5219_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_a_5210_);
                    v___x_5215_ = v_reuseFailAlloc_5219_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5213_ == 0 {
                    leanh::lean_ctor_set(v___x_5212_, 0, v___x_5215_);
                    v___x_5217_ = v___x_5212_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5218_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 0, v___x_5215_);
                    v___x_5217_ = v_reuseFailAlloc_5218_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5217_;
            }
            5 => {
                if v_isShared_5224_ == 0 {
                    v___x_5226_ = v___x_5223_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5227_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_a_5221_);
                    v___x_5226_ = v_reuseFailAlloc_5227_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5226_;
            }
            7 => {
                if v_isShared_5203_ == 0 {
                    leanh::lean_ctor_set(v___x_5202_, 0, v_a_5231_);
                    v___x_5236_ = v___x_5202_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5240_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5240_, 0, v_a_5231_);
                    v___x_5236_ = v_reuseFailAlloc_5240_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_5234_ == 0 {
                    leanh::lean_ctor_set(v___x_5233_, 0, v___x_5236_);
                    v___x_5238_ = v___x_5233_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5239_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5239_, 0, v___x_5236_);
                    v___x_5238_ = v_reuseFailAlloc_5239_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5238_;
            }
            10 => {
                if v_isShared_5245_ == 0 {
                    v___x_5247_ = v___x_5244_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5248_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5248_, 0, v_a_5242_);
                    v___x_5247_ = v_reuseFailAlloc_5248_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5247_;
            }
            12 => {
                v___x_5254_ = leanh::lean_box(0);
                if v_isShared_5253_ == 0 {
                    leanh::lean_ctor_set(v___x_5252_, 0, v___x_5254_);
                    v___x_5256_ = v___x_5252_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5257_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5257_, 0, v___x_5254_);
                    v___x_5256_ = v_reuseFailAlloc_5257_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5256_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg___boxed(
    mut v_binderName_5260_: *mut leanh::LeanObject,
    mut v_a_5261_: *mut leanh::LeanObject,
    mut v_a_5262_: *mut leanh::LeanObject,
    mut v_a_5263_: *mut leanh::LeanObject,
    mut v_a_5264_: *mut leanh::LeanObject,
    mut v_a_5265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5266_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(
        v_binderName_5260_,
        v_a_5261_,
        v_a_5262_,
        v_a_5263_,
        v_a_5264_,
    );
    leanh::lean_dec(v_a_5264_);
    leanh::lean_dec_ref(v_a_5263_);
    leanh::lean_dec(v_a_5262_);
    leanh::lean_dec_ref(v_a_5261_);
    return v_res_5266_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f(
    mut v_binderName_5267_: *mut leanh::LeanObject,
    mut v_a_5268_: *mut leanh::LeanObject,
    mut v_a_5269_: *mut leanh::LeanObject,
    mut v_a_5270_: *mut leanh::LeanObject,
    mut v_a_5271_: *mut leanh::LeanObject,
    mut v_a_5272_: *mut leanh::LeanObject,
    mut v_a_5273_: *mut leanh::LeanObject,
    mut v_a_5274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5276_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(
        v_binderName_5267_,
        v_a_5268_,
        v_a_5270_,
        v_a_5273_,
        v_a_5274_,
    );
    return v___x_5276_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___boxed(
    mut v_binderName_5277_: *mut leanh::LeanObject,
    mut v_a_5278_: *mut leanh::LeanObject,
    mut v_a_5279_: *mut leanh::LeanObject,
    mut v_a_5280_: *mut leanh::LeanObject,
    mut v_a_5281_: *mut leanh::LeanObject,
    mut v_a_5282_: *mut leanh::LeanObject,
    mut v_a_5283_: *mut leanh::LeanObject,
    mut v_a_5284_: *mut leanh::LeanObject,
    mut v_a_5285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5286_ = l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f(
        v_binderName_5277_,
        v_a_5278_,
        v_a_5279_,
        v_a_5280_,
        v_a_5281_,
        v_a_5282_,
        v_a_5283_,
        v_a_5284_,
    );
    leanh::lean_dec(v_a_5284_);
    leanh::lean_dec_ref(v_a_5283_);
    leanh::lean_dec(v_a_5282_);
    leanh::lean_dec_ref(v_a_5281_);
    leanh::lean_dec(v_a_5280_);
    leanh::lean_dec(v_a_5279_);
    leanh::lean_dec_ref(v_a_5278_);
    return v_res_5286_;
}
pub unsafe fn l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0(
    mut v_a_5287_: *mut leanh::LeanObject,
    mut v_x_5288_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5289_: u8 = 0;
    let mut v_head_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5288_) == 0 {
                    v___x_5289_ = 0;
                    return v___x_5289_;
                } else {
                    v_head_5290_ = leanh::lean_ctor_get(v_x_5288_, 0);
                    v_tail_5291_ = leanh::lean_ctor_get(v_x_5288_, 1);
                    v___x_5292_ = lean_expr_eqv(v_a_5287_, v_head_5290_);
                    if v___x_5292_ == 0 {
                        v_x_5288_ = v_tail_5291_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5292_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0___boxed(
    mut v_a_5294_: *mut leanh::LeanObject,
    mut v_x_5295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5296_: u8 = 0;
    let mut v_r_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5296_ =
        l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0(v_a_5294_, v_x_5295_);
    leanh::lean_dec(v_x_5295_);
    leanh::lean_dec_ref(v_a_5294_);
    v_r_5297_ = leanh::lean_box((v_res_5296_) as usize);
    return v_r_5297_;
}
pub unsafe fn l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(
    mut v_fvars_5298_: *mut leanh::LeanObject,
    mut v_e_5299_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5300_: u8 = 0;
    let mut v_d_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: u8 = 0;
    let mut v_binderType_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: u8 = 0;
    let mut v___x_5316_: u8 = 0;
    let mut v_fn_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: u8 = 0;
    let mut v_struct_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: u8 = 0;
    let mut v___x_5327_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5300_ = l_Lean_Expr_hasFVar(v_e_5299_);
                if v___x_5300_ == 0 {
                    leanh::lean_dec_ref(v_e_5299_);
                    return v___x_5300_;
                } else {
                    match leanh::lean_obj_tag(v_e_5299_) {
                        7 => {
                            v_binderType_5306_ = leanh::lean_ctor_get(v_e_5299_, 1);
                            leanh::lean_inc_ref(v_binderType_5306_);
                            v_body_5307_ = leanh::lean_ctor_get(v_e_5299_, 2);
                            leanh::lean_inc_ref(v_body_5307_);
                            leanh::lean_dec_ref_known(v_e_5299_, 3);
                            v_d_5302_ = v_binderType_5306_;
                            v_b_5303_ = v_body_5307_;
                            state = 1;
                            continue;
                        }
                        6 => {
                            v_binderType_5308_ = leanh::lean_ctor_get(v_e_5299_, 1);
                            leanh::lean_inc_ref(v_binderType_5308_);
                            v_body_5309_ = leanh::lean_ctor_get(v_e_5299_, 2);
                            leanh::lean_inc_ref(v_body_5309_);
                            leanh::lean_dec_ref_known(v_e_5299_, 3);
                            v_d_5302_ = v_binderType_5308_;
                            v_b_5303_ = v_body_5309_;
                            state = 1;
                            continue;
                        }
                        10 => {
                            v_expr_5310_ = leanh::lean_ctor_get(v_e_5299_, 1);
                            leanh::lean_inc_ref(v_expr_5310_);
                            leanh::lean_dec_ref_known(v_e_5299_, 2);
                            v_e_5299_ = v_expr_5310_;
                            state = 0;
                            continue;
                        }
                        8 => {
                            v_type_5312_ = leanh::lean_ctor_get(v_e_5299_, 1);
                            leanh::lean_inc_ref(v_type_5312_);
                            v_value_5313_ = leanh::lean_ctor_get(v_e_5299_, 2);
                            leanh::lean_inc_ref(v_value_5313_);
                            v_body_5314_ = leanh::lean_ctor_get(v_e_5299_, 3);
                            leanh::lean_inc_ref(v_body_5314_);
                            leanh::lean_dec_ref_known(v_e_5299_, 4);
                            v___x_5315_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_5298_, v_type_5312_);
                            if v___x_5315_ == 0 {
                                v___x_5316_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_5298_, v_value_5313_);
                                if v___x_5316_ == 0 {
                                    v_e_5299_ = v_body_5314_;
                                    state = 0;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_body_5314_);
                                    return v___x_5300_;
                                }
                            } else {
                                leanh::lean_dec_ref(v_body_5314_);
                                leanh::lean_dec_ref(v_value_5313_);
                                return v___x_5300_;
                            }
                        }
                        5 => {
                            v_fn_5318_ = leanh::lean_ctor_get(v_e_5299_, 0);
                            leanh::lean_inc_ref(v_fn_5318_);
                            v_arg_5319_ = leanh::lean_ctor_get(v_e_5299_, 1);
                            leanh::lean_inc_ref(v_arg_5319_);
                            leanh::lean_dec_ref_known(v_e_5299_, 2);
                            v___x_5320_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_5298_, v_fn_5318_);
                            if v___x_5320_ == 0 {
                                v_e_5299_ = v_arg_5319_;
                                state = 0;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_arg_5319_);
                                return v___x_5300_;
                            }
                        }
                        11 => {
                            v_struct_5322_ = leanh::lean_ctor_get(v_e_5299_, 2);
                            leanh::lean_inc_ref(v_struct_5322_);
                            leanh::lean_dec_ref_known(v_e_5299_, 3);
                            v_e_5299_ = v_struct_5322_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v_fvarId_5324_ = leanh::lean_ctor_get(v_e_5299_, 0);
                            leanh::lean_inc(v_fvarId_5324_);
                            leanh::lean_dec_ref_known(v_e_5299_, 1);
                            v___x_5325_ = l_Lean_Expr_fvar___override(v_fvarId_5324_);
                            v___x_5326_ =
                                l_List_elem___at___00Lean_Meta_ExtractLets_extractable_spec__0(
                                    v___x_5325_,
                                    v_fvars_5298_,
                                );
                            leanh::lean_dec_ref(v___x_5325_);
                            return v___x_5326_;
                        }
                        _ => {
                            leanh::lean_dec_ref(v_e_5299_);
                            v___x_5327_ = 0;
                            return v___x_5327_;
                        }
                    }
                }
            }
            1 => {
                v___x_5304_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_5298_, v_d_5302_);
                if v___x_5304_ == 0 {
                    v_e_5299_ = v_b_5303_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_b_5303_);
                    return v___x_5300_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1___boxed(
    mut v_fvars_5328_: *mut leanh::LeanObject,
    mut v_e_5329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5330_: u8 = 0;
    let mut v_r_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5330_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_5328_, v_e_5329_);
    leanh::lean_dec(v_fvars_5328_);
    v_r_5331_ = leanh::lean_box((v_res_5330_) as usize);
    return v_r_5331_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_extractable(
    mut v_fvars_5332_: *mut leanh::LeanObject,
    mut v_e_5333_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5334_: u8 = 0;
    v___x_5334_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_extractable_spec__1(v_fvars_5332_, v_e_5333_);
    if v___x_5334_ == 0 {
        let mut v___x_5335_: u8 = 0;
        v___x_5335_ = 1;
        return v___x_5335_;
    } else {
        let mut v___x_5336_: u8 = 0;
        v___x_5336_ = 0;
        return v___x_5336_;
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_extractable___boxed(
    mut v_fvars_5337_: *mut leanh::LeanObject,
    mut v_e_5338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5339_: u8 = 0;
    let mut v_r_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5339_ = l_Lean_Meta_ExtractLets_extractable(v_fvars_5337_, v_e_5338_);
    leanh::lean_dec(v_fvars_5337_);
    v_r_5340_ = leanh::lean_box((v_res_5339_) as usize);
    return v_r_5340_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_isExtractableLet___redArg(
    mut v_fvars_5341_: *mut leanh::LeanObject,
    mut v_n_5342_: *mut leanh::LeanObject,
    mut v_t_5343_: *mut leanh::LeanObject,
    mut v_v_5344_: *mut leanh::LeanObject,
    mut v_a_5345_: *mut leanh::LeanObject,
    mut v_a_5346_: *mut leanh::LeanObject,
    mut v_a_5347_: *mut leanh::LeanObject,
    mut v_a_5348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lift_5352_: u8 = 0;
    let mut v___x_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: u8 = 0;
    let mut v___x_5359_: u8 = 0;
    let mut v___x_5360_: u8 = 0;
    let mut v___x_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5365_: u8 = 0;
    let mut v_val_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5372_: u8 = 0;
    let mut v_a_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5376_: u8 = 0;
    let mut v___x_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5356_ = l_Lean_Meta_ExtractLets_hasNextName___redArg(v_a_5345_, v_a_5346_);
                v_a_5357_ = leanh::lean_ctor_get(v___x_5356_, 0);
                leanh::lean_inc(v_a_5357_);
                leanh::lean_dec_ref(v___x_5356_);
                v___x_5358_ = (leanh::lean_unbox(v_a_5357_) as u8);
                leanh::lean_dec(v_a_5357_);
                if v___x_5358_ == 0 {
                    leanh::lean_dec_ref(v_v_5344_);
                    leanh::lean_dec_ref(v_t_5343_);
                    v___y_5351_ = v_a_5345_;
                    state = 1;
                    continue;
                } else {
                    v___x_5359_ = l_Lean_Meta_ExtractLets_extractable(v_fvars_5341_, v_t_5343_);
                    if v___x_5359_ == 0 {
                        leanh::lean_dec_ref(v_v_5344_);
                        v___y_5351_ = v_a_5345_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5360_ = l_Lean_Meta_ExtractLets_extractable(v_fvars_5341_, v_v_5344_);
                        if v___x_5360_ == 0 {
                            v___y_5351_ = v_a_5345_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_n_5342_);
                            v___x_5361_ =
                                l_Lean_Meta_ExtractLets_nextNameForBinderName_x3f___redArg(
                                    v_n_5342_, v_a_5345_, v_a_5346_, v_a_5347_, v_a_5348_,
                                );
                            if leanh::lean_obj_tag(v___x_5361_) == 0 {
                                v_a_5362_ = leanh::lean_ctor_get(v___x_5361_, 0);
                                v_isSharedCheck_5372_ =
                                    (!leanh::lean_is_exclusive(v___x_5361_)) as u8;
                                if v_isSharedCheck_5372_ == 0 {
                                    v___x_5364_ = v___x_5361_;
                                    v_isShared_5365_ = v_isSharedCheck_5372_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5362_);
                                    leanh::lean_dec(v___x_5361_);
                                    v___x_5364_ = leanh::lean_box(0);
                                    v_isShared_5365_ = v_isSharedCheck_5372_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_n_5342_);
                                v_a_5373_ = leanh::lean_ctor_get(v___x_5361_, 0);
                                v_isSharedCheck_5380_ =
                                    (!leanh::lean_is_exclusive(v___x_5361_)) as u8;
                                if v_isSharedCheck_5380_ == 0 {
                                    v___x_5375_ = v___x_5361_;
                                    v_isShared_5376_ = v_isSharedCheck_5380_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5373_);
                                    leanh::lean_dec(v___x_5361_);
                                    v___x_5375_ = leanh::lean_box(0);
                                    v_isShared_5376_ = v_isSharedCheck_5380_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v_lift_5352_ = leanh::lean_ctor_get_uint8(v___y_5351_, 10 as u32);
                v___x_5353_ = leanh::lean_box((v_lift_5352_) as usize);
                v___x_5354_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5354_, 0, v___x_5353_);
                leanh::lean_ctor_set(v___x_5354_, 1, v_n_5342_);
                v___x_5355_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5355_, 0, v___x_5354_);
                return v___x_5355_;
            }
            2 => {
                if leanh::lean_obj_tag(v_a_5362_) == 1 {
                    leanh::lean_dec(v_n_5342_);
                    v_val_5366_ = leanh::lean_ctor_get(v_a_5362_, 0);
                    leanh::lean_inc(v_val_5366_);
                    leanh::lean_dec_ref_known(v_a_5362_, 1);
                    v___x_5367_ = leanh::lean_box((v___x_5359_) as usize);
                    v___x_5368_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5368_, 0, v___x_5367_);
                    leanh::lean_ctor_set(v___x_5368_, 1, v_val_5366_);
                    if v_isShared_5365_ == 0 {
                        leanh::lean_ctor_set(v___x_5364_, 0, v___x_5368_);
                        v___x_5370_ = v___x_5364_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5371_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5371_, 0, v___x_5368_);
                        v___x_5370_ = v_reuseFailAlloc_5371_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5364_);
                    leanh::lean_dec(v_a_5362_);
                    v___y_5351_ = v_a_5345_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_5370_;
            }
            4 => {
                if v_isShared_5376_ == 0 {
                    v___x_5378_ = v___x_5375_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5379_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5379_, 0, v_a_5373_);
                    v___x_5378_ = v_reuseFailAlloc_5379_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_isExtractableLet___redArg___boxed(
    mut v_fvars_5381_: *mut leanh::LeanObject,
    mut v_n_5382_: *mut leanh::LeanObject,
    mut v_t_5383_: *mut leanh::LeanObject,
    mut v_v_5384_: *mut leanh::LeanObject,
    mut v_a_5385_: *mut leanh::LeanObject,
    mut v_a_5386_: *mut leanh::LeanObject,
    mut v_a_5387_: *mut leanh::LeanObject,
    mut v_a_5388_: *mut leanh::LeanObject,
    mut v_a_5389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5390_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(
        v_fvars_5381_,
        v_n_5382_,
        v_t_5383_,
        v_v_5384_,
        v_a_5385_,
        v_a_5386_,
        v_a_5387_,
        v_a_5388_,
    );
    leanh::lean_dec(v_a_5388_);
    leanh::lean_dec_ref(v_a_5387_);
    leanh::lean_dec(v_a_5386_);
    leanh::lean_dec_ref(v_a_5385_);
    leanh::lean_dec(v_fvars_5381_);
    return v_res_5390_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_isExtractableLet(
    mut v_fvars_5391_: *mut leanh::LeanObject,
    mut v_n_5392_: *mut leanh::LeanObject,
    mut v_t_5393_: *mut leanh::LeanObject,
    mut v_v_5394_: *mut leanh::LeanObject,
    mut v_a_5395_: *mut leanh::LeanObject,
    mut v_a_5396_: *mut leanh::LeanObject,
    mut v_a_5397_: *mut leanh::LeanObject,
    mut v_a_5398_: *mut leanh::LeanObject,
    mut v_a_5399_: *mut leanh::LeanObject,
    mut v_a_5400_: *mut leanh::LeanObject,
    mut v_a_5401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5403_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(
        v_fvars_5391_,
        v_n_5392_,
        v_t_5393_,
        v_v_5394_,
        v_a_5395_,
        v_a_5397_,
        v_a_5400_,
        v_a_5401_,
    );
    return v___x_5403_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_isExtractableLet___boxed(
    mut v_fvars_5404_: *mut leanh::LeanObject,
    mut v_n_5405_: *mut leanh::LeanObject,
    mut v_t_5406_: *mut leanh::LeanObject,
    mut v_v_5407_: *mut leanh::LeanObject,
    mut v_a_5408_: *mut leanh::LeanObject,
    mut v_a_5409_: *mut leanh::LeanObject,
    mut v_a_5410_: *mut leanh::LeanObject,
    mut v_a_5411_: *mut leanh::LeanObject,
    mut v_a_5412_: *mut leanh::LeanObject,
    mut v_a_5413_: *mut leanh::LeanObject,
    mut v_a_5414_: *mut leanh::LeanObject,
    mut v_a_5415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5416_ = l_Lean_Meta_ExtractLets_isExtractableLet(
        v_fvars_5404_,
        v_n_5405_,
        v_t_5406_,
        v_v_5407_,
        v_a_5408_,
        v_a_5409_,
        v_a_5410_,
        v_a_5411_,
        v_a_5412_,
        v_a_5413_,
        v_a_5414_,
    );
    leanh::lean_dec(v_a_5414_);
    leanh::lean_dec_ref(v_a_5413_);
    leanh::lean_dec(v_a_5412_);
    leanh::lean_dec_ref(v_a_5411_);
    leanh::lean_dec(v_a_5410_);
    leanh::lean_dec(v_a_5409_);
    leanh::lean_dec_ref(v_a_5408_);
    leanh::lean_dec(v_fvars_5404_);
    return v_res_5416_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(
    mut v_a_5417_: *mut leanh::LeanObject,
    mut v_x_5418_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5419_: u8 = 0;
    let mut v_key_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5418_) == 0 {
                    v___x_5419_ = 0;
                    return v___x_5419_;
                } else {
                    v_key_5420_ = leanh::lean_ctor_get(v_x_5418_, 0);
                    v_tail_5421_ = leanh::lean_ctor_get(v_x_5418_, 2);
                    v___x_5422_ = l_Lean_ExprStructEq_beq(v_key_5420_, v_a_5417_);
                    if v___x_5422_ == 0 {
                        v_x_5418_ = v_tail_5421_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5422_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg___boxed(
    mut v_a_5424_: *mut leanh::LeanObject,
    mut v_x_5425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5426_: u8 = 0;
    let mut v_r_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5426_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(v_a_5424_, v_x_5425_);
    leanh::lean_dec(v_x_5425_);
    leanh::lean_dec_ref(v_a_5424_);
    v_r_5427_ = leanh::lean_box((v_res_5426_) as usize);
    return v_r_5427_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2___redArg(
    mut v_a_5428_: *mut leanh::LeanObject,
    mut v_b_5429_: *mut leanh::LeanObject,
    mut v_x_5430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5436_: u8 = 0;
    let mut v___x_5437_: u8 = 0;
    let mut v___x_5438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5445_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5430_) == 0 {
                    leanh::lean_dec(v_b_5429_);
                    leanh::lean_dec_ref(v_a_5428_);
                    return v_x_5430_;
                } else {
                    v_key_5431_ = leanh::lean_ctor_get(v_x_5430_, 0);
                    v_value_5432_ = leanh::lean_ctor_get(v_x_5430_, 1);
                    v_tail_5433_ = leanh::lean_ctor_get(v_x_5430_, 2);
                    v_isSharedCheck_5445_ = (!leanh::lean_is_exclusive(v_x_5430_)) as u8;
                    if v_isSharedCheck_5445_ == 0 {
                        v___x_5435_ = v_x_5430_;
                        v_isShared_5436_ = v_isSharedCheck_5445_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5433_);
                        leanh::lean_inc(v_value_5432_);
                        leanh::lean_inc(v_key_5431_);
                        leanh::lean_dec(v_x_5430_);
                        v___x_5435_ = leanh::lean_box(0);
                        v_isShared_5436_ = v_isSharedCheck_5445_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5437_ = l_Lean_ExprStructEq_beq(v_key_5431_, v_a_5428_);
                if v___x_5437_ == 0 {
                    v___x_5438_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2___redArg(v_a_5428_, v_b_5429_, v_tail_5433_);
                    if v_isShared_5436_ == 0 {
                        leanh::lean_ctor_set(v___x_5435_, 2, v___x_5438_);
                        v___x_5440_ = v___x_5435_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5441_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5441_, 0, v_key_5431_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5441_, 1, v_value_5432_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5441_, 2, v___x_5438_);
                        v___x_5440_ = v_reuseFailAlloc_5441_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_5432_);
                    leanh::lean_dec(v_key_5431_);
                    if v_isShared_5436_ == 0 {
                        leanh::lean_ctor_set(v___x_5435_, 1, v_b_5429_);
                        leanh::lean_ctor_set(v___x_5435_, 0, v_a_5428_);
                        v___x_5443_ = v___x_5435_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5444_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5444_, 0, v_a_5428_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5444_, 1, v_b_5429_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5444_, 2, v_tail_5433_);
                        v___x_5443_ = v_reuseFailAlloc_5444_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5440_;
            }
            3 => {
                return v___x_5443_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_5446_: *mut leanh::LeanObject,
    mut v_x_5447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_5448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5453_: u8 = 0;
    let mut v___x_5454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: u64 = 0;
    let mut v___x_5456_: u64 = 0;
    let mut v___x_5457_: u64 = 0;
    let mut v_fold_5458_: u64 = 0;
    let mut v___x_5459_: u64 = 0;
    let mut v___x_5460_: u64 = 0;
    let mut v___x_5461_: u64 = 0;
    let mut v___x_5462_: usize = 0;
    let mut v___x_5463_: usize = 0;
    let mut v___x_5464_: usize = 0;
    let mut v___x_5465_: usize = 0;
    let mut v___x_5466_: usize = 0;
    let mut v___x_5467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5447_) == 0 {
                    return v_x_5446_;
                } else {
                    v_key_5448_ = leanh::lean_ctor_get(v_x_5447_, 0);
                    v_value_5449_ = leanh::lean_ctor_get(v_x_5447_, 1);
                    v_tail_5450_ = leanh::lean_ctor_get(v_x_5447_, 2);
                    v_isSharedCheck_5473_ = (!leanh::lean_is_exclusive(v_x_5447_)) as u8;
                    if v_isSharedCheck_5473_ == 0 {
                        v___x_5452_ = v_x_5447_;
                        v_isShared_5453_ = v_isSharedCheck_5473_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5450_);
                        leanh::lean_inc(v_value_5449_);
                        leanh::lean_inc(v_key_5448_);
                        leanh::lean_dec(v_x_5447_);
                        v___x_5452_ = leanh::lean_box(0);
                        v_isShared_5453_ = v_isSharedCheck_5473_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5454_ = lean_array_get_size(v_x_5446_);
                v___x_5455_ = l_Lean_ExprStructEq_hash(v_key_5448_);
                v___x_5456_ = 32u64;
                v___x_5457_ = lean_uint64_shift_right(v___x_5455_, v___x_5456_);
                v_fold_5458_ = lean_uint64_xor(v___x_5455_, v___x_5457_);
                v___x_5459_ = 16u64;
                v___x_5460_ = lean_uint64_shift_right(v_fold_5458_, v___x_5459_);
                v___x_5461_ = lean_uint64_xor(v_fold_5458_, v___x_5460_);
                v___x_5462_ = lean_uint64_to_usize(v___x_5461_);
                v___x_5463_ = lean_usize_of_nat(v___x_5454_);
                v___x_5464_ = 1usize;
                v___x_5465_ = lean_usize_sub(v___x_5463_, v___x_5464_);
                v___x_5466_ = lean_usize_land(v___x_5462_, v___x_5465_);
                v___x_5467_ = lean_array_uget_borrowed(v_x_5446_, v___x_5466_);
                leanh::lean_inc(v___x_5467_);
                if v_isShared_5453_ == 0 {
                    leanh::lean_ctor_set(v___x_5452_, 2, v___x_5467_);
                    v___x_5469_ = v___x_5452_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5472_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5472_, 0, v_key_5448_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5472_, 1, v_value_5449_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5472_, 2, v___x_5467_);
                    v___x_5469_ = v_reuseFailAlloc_5472_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5470_ = lean_array_uset(v_x_5446_, v___x_5466_, v___x_5469_);
                v_x_5446_ = v___x_5470_;
                v_x_5447_ = v_tail_5450_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2___redArg(
    mut v_i_5474_: *mut leanh::LeanObject,
    mut v_source_5475_: *mut leanh::LeanObject,
    mut v_target_5476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5478_: u8 = 0;
    let mut v_es_5479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_5482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5477_ = lean_array_get_size(v_source_5475_);
                v___x_5478_ = lean_nat_dec_lt(v_i_5474_, v___x_5477_);
                if v___x_5478_ == 0 {
                    leanh::lean_dec_ref(v_source_5475_);
                    leanh::lean_dec(v_i_5474_);
                    return v_target_5476_;
                } else {
                    v_es_5479_ = lean_array_fget(v_source_5475_, v_i_5474_);
                    v___x_5480_ = leanh::lean_box(0);
                    v_source_5481_ = lean_array_fset(v_source_5475_, v_i_5474_, v___x_5480_);
                    v_target_5482_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2_spec__3___redArg(v_target_5476_, v_es_5479_);
                    v___x_5483_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5484_ = lean_nat_add(v_i_5474_, v___x_5483_);
                    leanh::lean_dec(v_i_5474_);
                    v_i_5474_ = v___x_5484_;
                    v_source_5475_ = v_source_5481_;
                    v_target_5476_ = v_target_5482_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1___redArg(
    mut v_data_5486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5487_ = lean_array_get_size(v_data_5486_);
    v___x_5488_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_5489_ = lean_nat_mul(v___x_5487_, v___x_5488_);
    v___x_5490_ = leanh::lean_unsigned_to_nat(0);
    v___x_5491_ = leanh::lean_box(0);
    v___x_5492_ = lean_mk_array(v_nbuckets_5489_, v___x_5491_);
    v___x_5493_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2___redArg(v___x_5490_, v_data_5486_, v___x_5492_);
    return v___x_5493_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(
    mut v_m_5494_: *mut leanh::LeanObject,
    mut v_a_5495_: *mut leanh::LeanObject,
    mut v_b_5496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_5497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5501_: u8 = 0;
    let mut v___x_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: u64 = 0;
    let mut v___x_5504_: u64 = 0;
    let mut v___x_5505_: u64 = 0;
    let mut v_fold_5506_: u64 = 0;
    let mut v___x_5507_: u64 = 0;
    let mut v___x_5508_: u64 = 0;
    let mut v___x_5509_: u64 = 0;
    let mut v___x_5510_: usize = 0;
    let mut v___x_5511_: usize = 0;
    let mut v___x_5512_: usize = 0;
    let mut v___x_5513_: usize = 0;
    let mut v___x_5514_: usize = 0;
    let mut v_bkt_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: u8 = 0;
    let mut v___x_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: u8 = 0;
    let mut v_val_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5541_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5497_ = leanh::lean_ctor_get(v_m_5494_, 0);
                v_buckets_5498_ = leanh::lean_ctor_get(v_m_5494_, 1);
                v_isSharedCheck_5541_ = (!leanh::lean_is_exclusive(v_m_5494_)) as u8;
                if v_isSharedCheck_5541_ == 0 {
                    v___x_5500_ = v_m_5494_;
                    v_isShared_5501_ = v_isSharedCheck_5541_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_5498_);
                    leanh::lean_inc(v_size_5497_);
                    leanh::lean_dec(v_m_5494_);
                    v___x_5500_ = leanh::lean_box(0);
                    v_isShared_5501_ = v_isSharedCheck_5541_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5502_ = lean_array_get_size(v_buckets_5498_);
                v___x_5503_ = l_Lean_ExprStructEq_hash(v_a_5495_);
                v___x_5504_ = 32u64;
                v___x_5505_ = lean_uint64_shift_right(v___x_5503_, v___x_5504_);
                v_fold_5506_ = lean_uint64_xor(v___x_5503_, v___x_5505_);
                v___x_5507_ = 16u64;
                v___x_5508_ = lean_uint64_shift_right(v_fold_5506_, v___x_5507_);
                v___x_5509_ = lean_uint64_xor(v_fold_5506_, v___x_5508_);
                v___x_5510_ = lean_uint64_to_usize(v___x_5509_);
                v___x_5511_ = lean_usize_of_nat(v___x_5502_);
                v___x_5512_ = 1usize;
                v___x_5513_ = lean_usize_sub(v___x_5511_, v___x_5512_);
                v___x_5514_ = lean_usize_land(v___x_5510_, v___x_5513_);
                v_bkt_5515_ = lean_array_uget_borrowed(v_buckets_5498_, v___x_5514_);
                v___x_5516_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(v_a_5495_, v_bkt_5515_);
                if v___x_5516_ == 0 {
                    v___x_5517_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_5518_ = lean_nat_add(v_size_5497_, v___x_5517_);
                    leanh::lean_dec(v_size_5497_);
                    leanh::lean_inc(v_bkt_5515_);
                    v___x_5519_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_5519_, 0, v_a_5495_);
                    leanh::lean_ctor_set(v___x_5519_, 1, v_b_5496_);
                    leanh::lean_ctor_set(v___x_5519_, 2, v_bkt_5515_);
                    v_buckets_x27_5520_ =
                        lean_array_uset(v_buckets_5498_, v___x_5514_, v___x_5519_);
                    v___x_5521_ = leanh::lean_unsigned_to_nat(4);
                    v___x_5522_ = lean_nat_mul(v_size_x27_5518_, v___x_5521_);
                    v___x_5523_ = leanh::lean_unsigned_to_nat(3);
                    v___x_5524_ = lean_nat_div(v___x_5522_, v___x_5523_);
                    leanh::lean_dec(v___x_5522_);
                    v___x_5525_ = lean_array_get_size(v_buckets_x27_5520_);
                    v___x_5526_ = lean_nat_dec_le(v___x_5524_, v___x_5525_);
                    leanh::lean_dec(v___x_5524_);
                    if v___x_5526_ == 0 {
                        v_val_5527_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1___redArg(v_buckets_x27_5520_);
                        if v_isShared_5501_ == 0 {
                            leanh::lean_ctor_set(v___x_5500_, 1, v_val_5527_);
                            leanh::lean_ctor_set(v___x_5500_, 0, v_size_x27_5518_);
                            v___x_5529_ = v___x_5500_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5530_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_5530_,
                                0,
                                v_size_x27_5518_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_5530_, 1, v_val_5527_);
                            v___x_5529_ = v_reuseFailAlloc_5530_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_5501_ == 0 {
                            leanh::lean_ctor_set(v___x_5500_, 1, v_buckets_x27_5520_);
                            leanh::lean_ctor_set(v___x_5500_, 0, v_size_x27_5518_);
                            v___x_5532_ = v___x_5500_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5533_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_5533_,
                                0,
                                v_size_x27_5518_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_5533_,
                                1,
                                v_buckets_x27_5520_,
                            );
                            v___x_5532_ = v_reuseFailAlloc_5533_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_5515_);
                    v___x_5534_ = leanh::lean_box(0);
                    v_buckets_x27_5535_ =
                        lean_array_uset(v_buckets_5498_, v___x_5514_, v___x_5534_);
                    v___x_5536_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2___redArg(v_a_5495_, v_b_5496_, v_bkt_5515_);
                    v___x_5537_ = lean_array_uset(v_buckets_x27_5535_, v___x_5514_, v___x_5536_);
                    if v_isShared_5501_ == 0 {
                        leanh::lean_ctor_set(v___x_5500_, 1, v___x_5537_);
                        v___x_5539_ = v___x_5500_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5540_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5540_, 0, v_size_5497_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5540_, 1, v___x_5537_);
                        v___x_5539_ = v_reuseFailAlloc_5540_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5529_;
            }
            3 => {
                return v___x_5532_;
            }
            4 => {
                return v___x_5539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_addDecl___redArg(
    mut v_decl_5542_: *mut leanh::LeanObject,
    mut v_isLet_5543_: u8,
    mut v_a_5544_: *mut leanh::LeanObject,
    mut v_a_5545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_givenNames_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_valueMap_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5558_: u8 = 0;
    let mut v_merge_5559_: u8 = 0;
    let mut v___x_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: u8 = 0;
    let mut v___x_5567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5573_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5547_ = lean_st_ref_take(v_a_5545_);
                v_givenNames_5553_ = leanh::lean_ctor_get(v___x_5547_, 0);
                v_decls_5554_ = leanh::lean_ctor_get(v___x_5547_, 1);
                v_valueMap_5555_ = leanh::lean_ctor_get(v___x_5547_, 2);
                v_isSharedCheck_5573_ = (!leanh::lean_is_exclusive(v___x_5547_)) as u8;
                if v_isSharedCheck_5573_ == 0 {
                    v___x_5557_ = v___x_5547_;
                    v_isShared_5558_ = v_isSharedCheck_5573_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_valueMap_5555_);
                    leanh::lean_inc(v_decls_5554_);
                    leanh::lean_inc(v_givenNames_5553_);
                    leanh::lean_dec(v___x_5547_);
                    v___x_5557_ = leanh::lean_box(0);
                    v_isShared_5558_ = v_isSharedCheck_5573_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_5551_ = lean_st_ref_set(v_a_5545_, v_snd_5550_);
                v___x_5552_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5552_, 0, v_fst_5549_);
                return v___x_5552_;
            }
            2 => {
                v_merge_5559_ = leanh::lean_ctor_get_uint8(v_a_5544_, 6 as u32);
                v___x_5560_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_decl_5542_);
                v___x_5561_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_5561_, 0, v_decl_5542_);
                leanh::lean_ctor_set_uint8(
                    v___x_5561_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_isLet_5543_,
                );
                v___x_5562_ = lean_array_push(v_decls_5554_, v___x_5561_);
                if v_merge_5559_ == 0 {
                    leanh::lean_dec_ref(v_decl_5542_);
                    if v_isShared_5558_ == 0 {
                        leanh::lean_ctor_set(v___x_5557_, 1, v___x_5562_);
                        v___x_5564_ = v___x_5557_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5565_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_givenNames_5553_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5565_, 1, v___x_5562_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5565_, 2, v_valueMap_5555_);
                        v___x_5564_ = v_reuseFailAlloc_5565_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_5566_ = 0;
                    v___x_5567_ = l_Lean_LocalDecl_value(v_decl_5542_, v___x_5566_);
                    v___x_5568_ = l_Lean_LocalDecl_fvarId(v_decl_5542_);
                    leanh::lean_dec_ref(v_decl_5542_);
                    v___x_5569_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_5555_, v___x_5567_, v___x_5568_);
                    if v_isShared_5558_ == 0 {
                        leanh::lean_ctor_set(v___x_5557_, 2, v___x_5569_);
                        leanh::lean_ctor_set(v___x_5557_, 1, v___x_5562_);
                        v___x_5571_ = v___x_5557_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5572_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5572_, 0, v_givenNames_5553_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5572_, 1, v___x_5562_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5572_, 2, v___x_5569_);
                        v___x_5571_ = v_reuseFailAlloc_5572_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_5549_ = v___x_5560_;
                v_snd_5550_ = v___x_5564_;
                state = 1;
                continue;
            }
            4 => {
                v_fst_5549_ = v___x_5560_;
                v_snd_5550_ = v___x_5571_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_addDecl___redArg___boxed(
    mut v_decl_5574_: *mut leanh::LeanObject,
    mut v_isLet_5575_: *mut leanh::LeanObject,
    mut v_a_5576_: *mut leanh::LeanObject,
    mut v_a_5577_: *mut leanh::LeanObject,
    mut v_a_5578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isLet_boxed_5579_: u8 = 0;
    let mut v_res_5580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLet_boxed_5579_ = (leanh::lean_unbox(v_isLet_5575_) as u8);
    v_res_5580_ = l_Lean_Meta_ExtractLets_addDecl___redArg(
        v_decl_5574_,
        v_isLet_boxed_5579_,
        v_a_5576_,
        v_a_5577_,
    );
    leanh::lean_dec(v_a_5577_);
    leanh::lean_dec_ref(v_a_5576_);
    return v_res_5580_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_addDecl(
    mut v_decl_5581_: *mut leanh::LeanObject,
    mut v_isLet_5582_: u8,
    mut v_a_5583_: *mut leanh::LeanObject,
    mut v_a_5584_: *mut leanh::LeanObject,
    mut v_a_5585_: *mut leanh::LeanObject,
    mut v_a_5586_: *mut leanh::LeanObject,
    mut v_a_5587_: *mut leanh::LeanObject,
    mut v_a_5588_: *mut leanh::LeanObject,
    mut v_a_5589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5591_ =
        l_Lean_Meta_ExtractLets_addDecl___redArg(v_decl_5581_, v_isLet_5582_, v_a_5583_, v_a_5585_);
    return v___x_5591_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_addDecl___boxed(
    mut v_decl_5592_: *mut leanh::LeanObject,
    mut v_isLet_5593_: *mut leanh::LeanObject,
    mut v_a_5594_: *mut leanh::LeanObject,
    mut v_a_5595_: *mut leanh::LeanObject,
    mut v_a_5596_: *mut leanh::LeanObject,
    mut v_a_5597_: *mut leanh::LeanObject,
    mut v_a_5598_: *mut leanh::LeanObject,
    mut v_a_5599_: *mut leanh::LeanObject,
    mut v_a_5600_: *mut leanh::LeanObject,
    mut v_a_5601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isLet_boxed_5602_: u8 = 0;
    let mut v_res_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLet_boxed_5602_ = (leanh::lean_unbox(v_isLet_5593_) as u8);
    v_res_5603_ = l_Lean_Meta_ExtractLets_addDecl(
        v_decl_5592_,
        v_isLet_boxed_5602_,
        v_a_5594_,
        v_a_5595_,
        v_a_5596_,
        v_a_5597_,
        v_a_5598_,
        v_a_5599_,
        v_a_5600_,
    );
    leanh::lean_dec(v_a_5600_);
    leanh::lean_dec_ref(v_a_5599_);
    leanh::lean_dec(v_a_5598_);
    leanh::lean_dec_ref(v_a_5597_);
    leanh::lean_dec(v_a_5596_);
    leanh::lean_dec(v_a_5595_);
    leanh::lean_dec_ref(v_a_5594_);
    return v_res_5603_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0(
    mut v_00_u03b2_5604_: *mut leanh::LeanObject,
    mut v_m_5605_: *mut leanh::LeanObject,
    mut v_a_5606_: *mut leanh::LeanObject,
    mut v_b_5607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5608_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_m_5605_, v_a_5606_, v_b_5607_);
    return v___x_5608_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0(
    mut v_00_u03b2_5609_: *mut leanh::LeanObject,
    mut v_a_5610_: *mut leanh::LeanObject,
    mut v_x_5611_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5612_: u8 = 0;
    v___x_5612_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___redArg(v_a_5610_, v_x_5611_);
    return v___x_5612_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0___boxed(
    mut v_00_u03b2_5613_: *mut leanh::LeanObject,
    mut v_a_5614_: *mut leanh::LeanObject,
    mut v_x_5615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5616_: u8 = 0;
    let mut v_r_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5616_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__0(v_00_u03b2_5613_, v_a_5614_, v_x_5615_);
    leanh::lean_dec(v_x_5615_);
    leanh::lean_dec_ref(v_a_5614_);
    v_r_5617_ = leanh::lean_box((v_res_5616_) as usize);
    return v_r_5617_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1(
    mut v_00_u03b2_5618_: *mut leanh::LeanObject,
    mut v_data_5619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5620_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1___redArg(v_data_5619_);
    return v___x_5620_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2(
    mut v_00_u03b2_5621_: *mut leanh::LeanObject,
    mut v_a_5622_: *mut leanh::LeanObject,
    mut v_b_5623_: *mut leanh::LeanObject,
    mut v_x_5624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5625_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__2___redArg(v_a_5622_, v_b_5623_, v_x_5624_);
    return v___x_5625_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2(
    mut v_00_u03b2_5626_: *mut leanh::LeanObject,
    mut v_i_5627_: *mut leanh::LeanObject,
    mut v_source_5628_: *mut leanh::LeanObject,
    mut v_target_5629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5630_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2___redArg(v_i_5627_, v_source_5628_, v_target_5629_);
    return v___x_5630_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_5631_: *mut leanh::LeanObject,
    mut v_x_5632_: *mut leanh::LeanObject,
    mut v_x_5633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5634_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0_spec__1_spec__2_spec__3___redArg(v_x_5632_, v_x_5633_);
    return v___x_5634_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(
    mut v_k_5635_: *mut leanh::LeanObject,
    mut v_t_5636_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_5637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: u8 = 0;
    let mut v___x_5642_: u8 = 0;
    let mut v___x_5644_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_5636_) == 0 {
                    v_k_5637_ = leanh::lean_ctor_get(v_t_5636_, 1);
                    v_l_5638_ = leanh::lean_ctor_get(v_t_5636_, 3);
                    v_r_5639_ = leanh::lean_ctor_get(v_t_5636_, 4);
                    v___x_5640_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5635_, v_k_5637_);
                    match v___x_5640_ {
                        0 => {
                            v_t_5636_ = v_l_5638_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_5642_ = 1;
                            return v___x_5642_;
                        }
                        _ => {
                            v_t_5636_ = v_r_5639_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_5644_ = 0;
                    return v___x_5644_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg___boxed(
    mut v_k_5645_: *mut leanh::LeanObject,
    mut v_t_5646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5647_: u8 = 0;
    let mut v_r_5648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5647_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(v_k_5645_, v_t_5646_);
    leanh::lean_dec(v_t_5646_);
    leanh::lean_dec(v_k_5645_);
    v_r_5648_ = leanh::lean_box((v_res_5647_) as usize);
    return v_r_5648_;
}
pub unsafe fn l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(
    mut v___x_5649_: *mut leanh::LeanObject,
    mut v_e_5650_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5651_: u8 = 0;
    let mut v_d_5653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: u8 = 0;
    let mut v_binderType_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: u8 = 0;
    let mut v___x_5667_: u8 = 0;
    let mut v_fn_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: u8 = 0;
    let mut v_struct_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: u8 = 0;
    let mut v___x_5677_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5651_ = l_Lean_Expr_hasFVar(v_e_5650_);
                if v___x_5651_ == 0 {
                    return v___x_5651_;
                } else {
                    match leanh::lean_obj_tag(v_e_5650_) {
                        7 => {
                            v_binderType_5657_ = leanh::lean_ctor_get(v_e_5650_, 1);
                            v_body_5658_ = leanh::lean_ctor_get(v_e_5650_, 2);
                            v_d_5653_ = v_binderType_5657_;
                            v_b_5654_ = v_body_5658_;
                            state = 1;
                            continue;
                        }
                        6 => {
                            v_binderType_5659_ = leanh::lean_ctor_get(v_e_5650_, 1);
                            v_body_5660_ = leanh::lean_ctor_get(v_e_5650_, 2);
                            v_d_5653_ = v_binderType_5659_;
                            v_b_5654_ = v_body_5660_;
                            state = 1;
                            continue;
                        }
                        10 => {
                            v_expr_5661_ = leanh::lean_ctor_get(v_e_5650_, 1);
                            v_e_5650_ = v_expr_5661_;
                            state = 0;
                            continue;
                        }
                        8 => {
                            v_type_5663_ = leanh::lean_ctor_get(v_e_5650_, 1);
                            v_value_5664_ = leanh::lean_ctor_get(v_e_5650_, 2);
                            v_body_5665_ = leanh::lean_ctor_get(v_e_5650_, 3);
                            v___x_5666_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_5649_, v_type_5663_);
                            if v___x_5666_ == 0 {
                                v___x_5667_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_5649_, v_value_5664_);
                                if v___x_5667_ == 0 {
                                    v_e_5650_ = v_body_5665_;
                                    state = 0;
                                    continue;
                                } else {
                                    return v___x_5651_;
                                }
                            } else {
                                return v___x_5651_;
                            }
                        }
                        5 => {
                            v_fn_5669_ = leanh::lean_ctor_get(v_e_5650_, 0);
                            v_arg_5670_ = leanh::lean_ctor_get(v_e_5650_, 1);
                            v___x_5671_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_5649_, v_fn_5669_);
                            if v___x_5671_ == 0 {
                                v_e_5650_ = v_arg_5670_;
                                state = 0;
                                continue;
                            } else {
                                return v___x_5651_;
                            }
                        }
                        11 => {
                            v_struct_5673_ = leanh::lean_ctor_get(v_e_5650_, 2);
                            v_e_5650_ = v_struct_5673_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v_fvarId_5675_ = leanh::lean_ctor_get(v_e_5650_, 0);
                            v___x_5676_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(v_fvarId_5675_, v___x_5649_);
                            return v___x_5676_;
                        }
                        _ => {
                            v___x_5677_ = 0;
                            return v___x_5677_;
                        }
                    }
                }
            }
            1 => {
                v___x_5655_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_5649_, v_d_5653_);
                if v___x_5655_ == 0 {
                    v_e_5650_ = v_b_5654_;
                    state = 0;
                    continue;
                } else {
                    return v___x_5651_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1___boxed(
    mut v___x_5678_: *mut leanh::LeanObject,
    mut v_e_5679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5680_: u8 = 0;
    let mut v_r_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5680_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v___x_5678_, v_e_5679_);
    leanh::lean_dec_ref(v_e_5679_);
    leanh::lean_dec(v___x_5678_);
    v_r_5681_ = leanh::lean_box((v_res_5680_) as usize);
    return v_r_5681_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(
    mut v_as_5682_: *mut leanh::LeanObject,
    mut v_sz_5683_: usize,
    mut v_i_5684_: usize,
    mut v_b_5685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_5688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: usize = 0;
    let mut v___x_5690_: usize = 0;
    let mut v___x_5692_: u8 = 0;
    let mut v___x_5693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5698_: u8 = 0;
    let mut v_fst_5699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5703_: u8 = 0;
    let mut v_a_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_5705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5707_: u8 = 0;
    let mut v___x_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: u8 = 0;
    let mut v___x_5726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: u8 = 0;
    let mut v_isSharedCheck_5728_: u8 = 0;
    let mut v_isSharedCheck_5729_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5692_ = lean_usize_dec_lt(v_i_5684_, v_sz_5683_);
                if v___x_5692_ == 0 {
                    v___x_5693_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5693_, 0, v_b_5685_);
                    return v___x_5693_;
                } else {
                    v_snd_5694_ = leanh::lean_ctor_get(v_b_5685_, 1);
                    v_fst_5695_ = leanh::lean_ctor_get(v_b_5685_, 0);
                    v_isSharedCheck_5729_ = (!leanh::lean_is_exclusive(v_b_5685_)) as u8;
                    if v_isSharedCheck_5729_ == 0 {
                        v___x_5697_ = v_b_5685_;
                        v_isShared_5698_ = v_isSharedCheck_5729_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5694_);
                        leanh::lean_inc(v_fst_5695_);
                        leanh::lean_dec(v_b_5685_);
                        v___x_5697_ = leanh::lean_box(0);
                        v_isShared_5698_ = v_isSharedCheck_5729_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5689_ = 1usize;
                v___x_5690_ = lean_usize_add(v_i_5684_, v___x_5689_);
                v_i_5684_ = v___x_5690_;
                v_b_5685_ = v_a_5688_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_5699_ = leanh::lean_ctor_get(v_snd_5694_, 0);
                v_snd_5700_ = leanh::lean_ctor_get(v_snd_5694_, 1);
                v_isSharedCheck_5728_ = (!leanh::lean_is_exclusive(v_snd_5694_)) as u8;
                if v_isSharedCheck_5728_ == 0 {
                    v___x_5702_ = v_snd_5694_;
                    v_isShared_5703_ = v_isSharedCheck_5728_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_5700_);
                    leanh::lean_inc(v_fst_5699_);
                    leanh::lean_dec(v_snd_5694_);
                    v___x_5702_ = leanh::lean_box(0);
                    v_isShared_5703_ = v_isSharedCheck_5728_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_5704_ = lean_array_uget_borrowed(v_as_5682_, v_i_5684_);
                v_decl_5705_ = leanh::lean_ctor_get(v_a_5704_, 0);
                v___x_5724_ = l_Lean_LocalDecl_type(v_decl_5705_);
                v___x_5725_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v_fst_5695_, v___x_5724_);
                leanh::lean_dec_ref(v___x_5724_);
                if v___x_5725_ == 0 {
                    v___x_5726_ = l_Lean_LocalDecl_value(v_decl_5705_, v___x_5725_);
                    v___x_5727_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_ExtractLets_flushDecls_spec__1(v_fst_5695_, v___x_5726_);
                    leanh::lean_dec_ref(v___x_5726_);
                    v___y_5707_ = v___x_5727_;
                    state = 4;
                    continue;
                } else {
                    v___y_5707_ = v___x_5725_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_5707_ == 0 {
                    leanh::lean_inc(v_a_5704_);
                    v___x_5708_ = lean_array_push(v_fst_5699_, v_a_5704_);
                    if v_isShared_5703_ == 0 {
                        leanh::lean_ctor_set(v___x_5702_, 0, v___x_5708_);
                        v___x_5710_ = v___x_5702_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5714_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5714_, 0, v___x_5708_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5714_, 1, v_snd_5700_);
                        v___x_5710_ = v_reuseFailAlloc_5714_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_a_5704_);
                    v___x_5715_ = lean_array_push(v_snd_5700_, v_a_5704_);
                    v___x_5716_ = l_Lean_LocalDecl_fvarId(v_decl_5705_);
                    v___x_5717_ = l_Lean_FVarIdSet_insert(v_fst_5695_, v___x_5716_);
                    if v_isShared_5703_ == 0 {
                        leanh::lean_ctor_set(v___x_5702_, 1, v___x_5715_);
                        v___x_5719_ = v___x_5702_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5723_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5723_, 0, v_fst_5699_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5723_, 1, v___x_5715_);
                        v___x_5719_ = v_reuseFailAlloc_5723_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_5698_ == 0 {
                    leanh::lean_ctor_set(v___x_5697_, 1, v___x_5710_);
                    v___x_5712_ = v___x_5697_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5713_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5713_, 0, v_fst_5695_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5713_, 1, v___x_5710_);
                    v___x_5712_ = v_reuseFailAlloc_5713_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_5688_ = v___x_5712_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_5698_ == 0 {
                    leanh::lean_ctor_set(v___x_5697_, 1, v___x_5719_);
                    leanh::lean_ctor_set(v___x_5697_, 0, v___x_5717_);
                    v___x_5721_ = v___x_5697_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5722_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5722_, 0, v___x_5717_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5722_, 1, v___x_5719_);
                    v___x_5721_ = v_reuseFailAlloc_5722_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_a_5688_ = v___x_5721_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg___boxed(
    mut v_as_5730_: *mut leanh::LeanObject,
    mut v_sz_5731_: *mut leanh::LeanObject,
    mut v_i_5732_: *mut leanh::LeanObject,
    mut v_b_5733_: *mut leanh::LeanObject,
    mut v___y_5734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5735_: usize = 0;
    let mut v_i_boxed_5736_: usize = 0;
    let mut v_res_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5735_ = leanh::lean_unbox_usize(v_sz_5731_);
    leanh::lean_dec(v_sz_5731_);
    v_i_boxed_5736_ = leanh::lean_unbox_usize(v_i_5732_);
    leanh::lean_dec(v_i_5732_);
    v_res_5737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_as_5730_, v_sz_boxed_5735_, v_i_boxed_5736_, v_b_5733_);
    leanh::lean_dec_ref(v_as_5730_);
    return v_res_5737_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_flushDecls(
    mut v_fvar_5740_: *mut leanh::LeanObject,
    mut v_a_5741_: *mut leanh::LeanObject,
    mut v_a_5742_: *mut leanh::LeanObject,
    mut v_a_5743_: *mut leanh::LeanObject,
    mut v_a_5744_: *mut leanh::LeanObject,
    mut v_a_5745_: *mut leanh::LeanObject,
    mut v_a_5746_: *mut leanh::LeanObject,
    mut v_a_5747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_5750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarSet_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarSet_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5755_: usize = 0;
    let mut v___x_5756_: usize = 0;
    let mut v___x_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5761_: u8 = 0;
    let mut v___x_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_givenNames_5766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_valueMap_5767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5770_: u8 = 0;
    let mut v___x_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5778_: u8 = 0;
    let mut v_unused_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5780_: u8 = 0;
    let mut v_a_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5784_: u8 = 0;
    let mut v___x_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5788_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5749_ = lean_st_ref_get(v_a_5743_);
                v_decls_5750_ = leanh::lean_ctor_get(v___x_5749_, 1);
                leanh::lean_inc_ref(v_decls_5750_);
                leanh::lean_dec(v___x_5749_);
                v_fvarSet_5751_ = leanh::lean_box(1);
                v_fvarSet_5752_ = l_Lean_FVarIdSet_insert(v_fvarSet_5751_, v_fvar_5740_);
                v___x_5753_ = l_Lean_Meta_ExtractLets_flushDecls___closed__0;
                v___x_5754_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5754_, 0, v_fvarSet_5752_);
                leanh::lean_ctor_set(v___x_5754_, 1, v___x_5753_);
                v_sz_5755_ = lean_array_size(v_decls_5750_);
                v___x_5756_ = 0usize;
                v___x_5757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_decls_5750_, v_sz_5755_, v___x_5756_, v___x_5754_);
                leanh::lean_dec_ref(v_decls_5750_);
                if leanh::lean_obj_tag(v___x_5757_) == 0 {
                    v_a_5758_ = leanh::lean_ctor_get(v___x_5757_, 0);
                    v_isSharedCheck_5780_ = (!leanh::lean_is_exclusive(v___x_5757_)) as u8;
                    if v_isSharedCheck_5780_ == 0 {
                        v___x_5760_ = v___x_5757_;
                        v_isShared_5761_ = v_isSharedCheck_5780_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5758_);
                        leanh::lean_dec(v___x_5757_);
                        v___x_5760_ = leanh::lean_box(0);
                        v_isShared_5761_ = v_isSharedCheck_5780_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5781_ = leanh::lean_ctor_get(v___x_5757_, 0);
                    v_isSharedCheck_5788_ = (!leanh::lean_is_exclusive(v___x_5757_)) as u8;
                    if v_isSharedCheck_5788_ == 0 {
                        v___x_5783_ = v___x_5757_;
                        v_isShared_5784_ = v_isSharedCheck_5788_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5781_);
                        leanh::lean_dec(v___x_5757_);
                        v___x_5783_ = leanh::lean_box(0);
                        v_isShared_5784_ = v_isSharedCheck_5788_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5762_ = lean_st_ref_take(v_a_5743_);
                v_snd_5763_ = leanh::lean_ctor_get(v_a_5758_, 1);
                leanh::lean_inc(v_snd_5763_);
                leanh::lean_dec(v_a_5758_);
                v_fst_5764_ = leanh::lean_ctor_get(v_snd_5763_, 0);
                leanh::lean_inc(v_fst_5764_);
                v_snd_5765_ = leanh::lean_ctor_get(v_snd_5763_, 1);
                leanh::lean_inc(v_snd_5765_);
                leanh::lean_dec(v_snd_5763_);
                v_givenNames_5766_ = leanh::lean_ctor_get(v___x_5762_, 0);
                v_valueMap_5767_ = leanh::lean_ctor_get(v___x_5762_, 2);
                v_isSharedCheck_5778_ = (!leanh::lean_is_exclusive(v___x_5762_)) as u8;
                if v_isSharedCheck_5778_ == 0 {
                    v_unused_5779_ = leanh::lean_ctor_get(v___x_5762_, 1);
                    leanh::lean_dec(v_unused_5779_);
                    v___x_5769_ = v___x_5762_;
                    v_isShared_5770_ = v_isSharedCheck_5778_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_valueMap_5767_);
                    leanh::lean_inc(v_givenNames_5766_);
                    leanh::lean_dec(v___x_5762_);
                    v___x_5769_ = leanh::lean_box(0);
                    v_isShared_5770_ = v_isSharedCheck_5778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5770_ == 0 {
                    leanh::lean_ctor_set(v___x_5769_, 1, v_fst_5764_);
                    v___x_5772_ = v___x_5769_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5777_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5777_, 0, v_givenNames_5766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5777_, 1, v_fst_5764_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5777_, 2, v_valueMap_5767_);
                    v___x_5772_ = v_reuseFailAlloc_5777_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5773_ = lean_st_ref_set(v_a_5743_, v___x_5772_);
                if v_isShared_5761_ == 0 {
                    leanh::lean_ctor_set(v___x_5760_, 0, v_snd_5765_);
                    v___x_5775_ = v___x_5760_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5776_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5776_, 0, v_snd_5765_);
                    v___x_5775_ = v_reuseFailAlloc_5776_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5775_;
            }
            5 => {
                if v_isShared_5784_ == 0 {
                    v___x_5786_ = v___x_5783_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5787_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 0, v_a_5781_);
                    v___x_5786_ = v_reuseFailAlloc_5787_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5786_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_flushDecls___boxed(
    mut v_fvar_5789_: *mut leanh::LeanObject,
    mut v_a_5790_: *mut leanh::LeanObject,
    mut v_a_5791_: *mut leanh::LeanObject,
    mut v_a_5792_: *mut leanh::LeanObject,
    mut v_a_5793_: *mut leanh::LeanObject,
    mut v_a_5794_: *mut leanh::LeanObject,
    mut v_a_5795_: *mut leanh::LeanObject,
    mut v_a_5796_: *mut leanh::LeanObject,
    mut v_a_5797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5798_ = l_Lean_Meta_ExtractLets_flushDecls(
        v_fvar_5789_,
        v_a_5790_,
        v_a_5791_,
        v_a_5792_,
        v_a_5793_,
        v_a_5794_,
        v_a_5795_,
        v_a_5796_,
    );
    leanh::lean_dec(v_a_5796_);
    leanh::lean_dec_ref(v_a_5795_);
    leanh::lean_dec(v_a_5794_);
    leanh::lean_dec_ref(v_a_5793_);
    leanh::lean_dec(v_a_5792_);
    leanh::lean_dec(v_a_5791_);
    leanh::lean_dec_ref(v_a_5790_);
    return v_res_5798_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0(
    mut v_00_u03b2_5799_: *mut leanh::LeanObject,
    mut v_k_5800_: *mut leanh::LeanObject,
    mut v_t_5801_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5802_: u8 = 0;
    v___x_5802_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___redArg(v_k_5800_, v_t_5801_);
    return v___x_5802_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0___boxed(
    mut v_00_u03b2_5803_: *mut leanh::LeanObject,
    mut v_k_5804_: *mut leanh::LeanObject,
    mut v_t_5805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5806_: u8 = 0;
    let mut v_r_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5806_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_ExtractLets_flushDecls_spec__0(
            v_00_u03b2_5803_,
            v_k_5804_,
            v_t_5805_,
        );
    leanh::lean_dec(v_t_5805_);
    leanh::lean_dec(v_k_5804_);
    v_r_5807_ = leanh::lean_box((v_res_5806_) as usize);
    return v_r_5807_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2(
    mut v_as_5808_: *mut leanh::LeanObject,
    mut v_sz_5809_: usize,
    mut v_i_5810_: usize,
    mut v_b_5811_: *mut leanh::LeanObject,
    mut v___y_5812_: *mut leanh::LeanObject,
    mut v___y_5813_: *mut leanh::LeanObject,
    mut v___y_5814_: *mut leanh::LeanObject,
    mut v___y_5815_: *mut leanh::LeanObject,
    mut v___y_5816_: *mut leanh::LeanObject,
    mut v___y_5817_: *mut leanh::LeanObject,
    mut v___y_5818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___redArg(v_as_5808_, v_sz_5809_, v_i_5810_, v_b_5811_);
    return v___x_5820_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2___boxed(
    mut v_as_5821_: *mut leanh::LeanObject,
    mut v_sz_5822_: *mut leanh::LeanObject,
    mut v_i_5823_: *mut leanh::LeanObject,
    mut v_b_5824_: *mut leanh::LeanObject,
    mut v___y_5825_: *mut leanh::LeanObject,
    mut v___y_5826_: *mut leanh::LeanObject,
    mut v___y_5827_: *mut leanh::LeanObject,
    mut v___y_5828_: *mut leanh::LeanObject,
    mut v___y_5829_: *mut leanh::LeanObject,
    mut v___y_5830_: *mut leanh::LeanObject,
    mut v___y_5831_: *mut leanh::LeanObject,
    mut v___y_5832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5833_: usize = 0;
    let mut v_i_boxed_5834_: usize = 0;
    let mut v_res_5835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5833_ = leanh::lean_unbox_usize(v_sz_5822_);
    leanh::lean_dec(v_sz_5822_);
    v_i_boxed_5834_ = leanh::lean_unbox_usize(v_i_5823_);
    leanh::lean_dec(v_i_5823_);
    v_res_5835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ExtractLets_flushDecls_spec__2(v_as_5821_, v_sz_boxed_5833_, v_i_boxed_5834_, v_b_5824_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_, v___y_5831_);
    leanh::lean_dec(v___y_5831_);
    leanh::lean_dec_ref(v___y_5830_);
    leanh::lean_dec(v___y_5829_);
    leanh::lean_dec_ref(v___y_5828_);
    leanh::lean_dec(v___y_5827_);
    leanh::lean_dec(v___y_5826_);
    leanh::lean_dec_ref(v___y_5825_);
    leanh::lean_dec_ref(v_as_5821_);
    return v_res_5835_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0(
    mut v_x_5836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decl_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_decl_5837_ = leanh::lean_ctor_get(v_x_5836_, 0);
    leanh::lean_inc_ref(v_decl_5837_);
    return v_decl_5837_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0___boxed(
    mut v_x_5838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5839_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__0(v_x_5838_);
    leanh::lean_dec_ref(v_x_5838_);
    return v_res_5839_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1(
    mut v_lctx_5840_: *mut leanh::LeanObject,
    mut v_x1_5841_: *mut leanh::LeanObject,
    mut v_x2_5842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decl_5843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: u8 = 0;
    v_decl_5843_ = leanh::lean_ctor_get(v_x2_5842_, 0);
    v___x_5844_ = l_Lean_LocalDecl_fvarId(v_decl_5843_);
    v___x_5845_ = l_Lean_LocalContext_contains(v_lctx_5840_, v___x_5844_);
    leanh::lean_dec(v___x_5844_);
    if v___x_5845_ == 0 {
        let mut v___x_5846_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5846_ = lean_array_push(v_x1_5841_, v_x2_5842_);
        return v___x_5846_;
    } else {
        leanh::lean_dec_ref(v_x2_5842_);
        return v_x1_5841_;
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1___boxed(
    mut v_lctx_5847_: *mut leanh::LeanObject,
    mut v_x1_5848_: *mut leanh::LeanObject,
    mut v_x2_5849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5850_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1(
        v_lctx_5847_,
        v_x1_5848_,
        v_x2_5849_,
    );
    leanh::lean_dec_ref(v_lctx_5847_);
    return v_res_5850_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2(
    mut v___f_5870_: *mut leanh::LeanObject,
    mut v_inst_5871_: *mut leanh::LeanObject,
    mut v_inst_5872_: *mut leanh::LeanObject,
    mut v_k_5873_: *mut leanh::LeanObject,
    mut v_decls_5874_: *mut leanh::LeanObject,
    mut v_lctx_5875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5879_: usize = 0;
    let mut v___x_5880_: usize = 0;
    let mut v_decls_5881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: u8 = 0;
    let mut v___f_5889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: u8 = 0;
    let mut v___x_5891_: usize = 0;
    let mut v___x_5892_: usize = 0;
    let mut v___x_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: usize = 0;
    let mut v___x_5895_: usize = 0;
    let mut v___x_5896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5884_ = leanh::lean_unsigned_to_nat(0);
                v___x_5885_ = lean_array_get_size(v_decls_5874_);
                v___x_5886_ = l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0;
                v___x_5887_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9;
                v___x_5888_ = lean_nat_dec_lt(v___x_5884_, v___x_5885_);
                if v___x_5888_ == 0 {
                    leanh::lean_dec_ref(v_lctx_5875_);
                    leanh::lean_dec_ref(v_decls_5874_);
                    v___y_5877_ = v___x_5886_;
                    state = 1;
                    continue;
                } else {
                    v___f_5889_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    leanh::lean_closure_set(v___f_5889_, 0, v_lctx_5875_);
                    v___x_5890_ = lean_nat_dec_le(v___x_5885_, v___x_5885_);
                    if v___x_5890_ == 0 {
                        if v___x_5888_ == 0 {
                            leanh::lean_dec_ref(v___f_5889_);
                            leanh::lean_dec_ref(v_decls_5874_);
                            v___y_5877_ = v___x_5886_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5891_ = 0usize;
                            v___x_5892_ = lean_usize_of_nat(v___x_5885_);
                            v___x_5893_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_5887_,
                                    v___f_5889_,
                                    v_decls_5874_,
                                    v___x_5891_,
                                    v___x_5892_,
                                    v___x_5886_,
                                );
                            v___y_5877_ = v___x_5893_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_5894_ = 0usize;
                        v___x_5895_ = lean_usize_of_nat(v___x_5885_);
                        v___x_5896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_5887_,
                            v___f_5889_,
                            v_decls_5874_,
                            v___x_5894_,
                            v___x_5895_,
                            v___x_5886_,
                        );
                        v___y_5877_ = v___x_5896_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5878_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2___closed__9;
                v_sz_5879_ = lean_array_size(v___y_5877_);
                v___x_5880_ = 0usize;
                v_decls_5881_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_5878_,
                    v___f_5870_,
                    v_sz_5879_,
                    v___x_5880_,
                    v___y_5877_,
                );
                v___x_5882_ = lean_array_to_list(v_decls_5881_);
                v___x_5883_ = l_Lean_Meta_withExistingLocalDecls___redArg(
                    v_inst_5871_,
                    v_inst_5872_,
                    v___x_5882_,
                    v_k_5873_,
                );
                return v___x_5883_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg(
    mut v_inst_5898_: *mut leanh::LeanObject,
    mut v_inst_5899_: *mut leanh::LeanObject,
    mut v_inst_5900_: *mut leanh::LeanObject,
    mut v_decls_5901_: *mut leanh::LeanObject,
    mut v_k_5902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_5903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_5903_ = leanh::lean_ctor_get(v_inst_5898_, 1);
    leanh::lean_inc(v_toBind_5903_);
    v___f_5904_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___closed__0;
    v___f_5905_ = leanh::lean_alloc_closure(
        l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg___lam__2
            as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_5905_, 0, v___f_5904_);
    leanh::lean_closure_set(v___f_5905_, 1, v_inst_5899_);
    leanh::lean_closure_set(v___f_5905_, 2, v_inst_5898_);
    leanh::lean_closure_set(v___f_5905_, 3, v_k_5902_);
    leanh::lean_closure_set(v___f_5905_, 4, v_decls_5901_);
    v___x_5906_ = leanh::lean_apply_4(
        v_toBind_5903_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_5900_,
        v___f_5905_,
    );
    return v___x_5906_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext(
    mut v_m_5907_: *mut leanh::LeanObject,
    mut v_00_u03b1_5908_: *mut leanh::LeanObject,
    mut v_inst_5909_: *mut leanh::LeanObject,
    mut v_inst_5910_: *mut leanh::LeanObject,
    mut v_inst_5911_: *mut leanh::LeanObject,
    mut v_decls_5912_: *mut leanh::LeanObject,
    mut v_k_5913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5914_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___redArg(
        v_inst_5909_,
        v_inst_5910_,
        v_inst_5911_,
        v_decls_5912_,
        v_k_5913_,
    );
    return v___x_5914_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(
    mut v_as_5915_: *mut leanh::LeanObject,
    mut v_i_5916_: usize,
    mut v_stop_5917_: usize,
    mut v_b_5918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5919_: u8 = 0;
    let mut v___x_5920_: usize = 0;
    let mut v___x_5921_: usize = 0;
    let mut v___x_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_5923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isLet_5924_: u8 = 0;
    let mut v___x_5925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: u8 = 0;
    let mut v___x_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5919_ = lean_usize_dec_eq(v_i_5916_, v_stop_5917_);
                if v___x_5919_ == 0 {
                    v___x_5920_ = 1usize;
                    v___x_5921_ = lean_usize_sub(v_i_5916_, v___x_5920_);
                    v___x_5922_ = lean_array_uget_borrowed(v_as_5915_, v___x_5921_);
                    v_decl_5923_ = leanh::lean_ctor_get(v___x_5922_, 0);
                    v_isLet_5924_ = leanh::lean_ctor_get_uint8(
                        v___x_5922_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_5925_ = l_Lean_LocalDecl_userName(v_decl_5923_);
                    v___x_5926_ = l_Lean_LocalDecl_type(v_decl_5923_);
                    v___x_5927_ = l_Lean_LocalDecl_value(v_decl_5923_, v___x_5919_);
                    leanh::lean_inc_ref(v_decl_5923_);
                    v___x_5928_ = l_Lean_LocalDecl_toExpr(v_decl_5923_);
                    v___x_5929_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5930_ = lean_mk_empty_array_with_capacity(v___x_5929_);
                    v___x_5931_ = lean_array_push(v___x_5930_, v___x_5928_);
                    v___x_5932_ = lean_expr_abstract(v_b_5918_, v___x_5931_);
                    leanh::lean_dec_ref(v___x_5931_);
                    leanh::lean_dec_ref(v_b_5918_);
                    if v_isLet_5924_ == 0 {
                        v___x_5933_ = 1;
                        v___x_5934_ = l_Lean_Expr_letE___override(
                            v___x_5925_,
                            v___x_5926_,
                            v___x_5927_,
                            v___x_5932_,
                            v___x_5933_,
                        );
                        v_i_5916_ = v___x_5921_;
                        v_b_5918_ = v___x_5934_;
                        state = 0;
                        continue;
                    } else {
                        v___x_5936_ = l_Lean_Expr_letE___override(
                            v___x_5925_,
                            v___x_5926_,
                            v___x_5927_,
                            v___x_5932_,
                            v___x_5919_,
                        );
                        v_i_5916_ = v___x_5921_;
                        v_b_5918_ = v___x_5936_;
                        state = 0;
                        continue;
                    }
                } else {
                    return v_b_5918_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0___boxed(
    mut v_as_5938_: *mut leanh::LeanObject,
    mut v_i_5939_: *mut leanh::LeanObject,
    mut v_stop_5940_: *mut leanh::LeanObject,
    mut v_b_5941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5942_: usize = 0;
    let mut v_stop_boxed_5943_: usize = 0;
    let mut v_res_5944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5942_ = leanh::lean_unbox_usize(v_i_5939_);
    leanh::lean_dec(v_i_5939_);
    v_stop_boxed_5943_ = leanh::lean_unbox_usize(v_stop_5940_);
    leanh::lean_dec(v_stop_5940_);
    v_res_5944_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(v_as_5938_, v_i_boxed_5942_, v_stop_boxed_5943_, v_b_5941_);
    leanh::lean_dec_ref(v_as_5938_);
    return v_res_5944_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_mkLetDecls(
    mut v_decls_5945_: *mut leanh::LeanObject,
    mut v_e_5946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: u8 = 0;
    v___x_5947_ = lean_array_get_size(v_decls_5945_);
    v___x_5948_ = leanh::lean_unsigned_to_nat(0);
    v___x_5949_ = lean_nat_dec_lt(v___x_5948_, v___x_5947_);
    if v___x_5949_ == 0 {
        return v_e_5946_;
    } else {
        let mut v___x_5950_: usize = 0;
        let mut v___x_5951_: usize = 0;
        let mut v___x_5952_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5950_ = lean_usize_of_nat(v___x_5947_);
        v___x_5951_ = 0usize;
        v___x_5952_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_ExtractLets_mkLetDecls_spec__0(v_decls_5945_, v___x_5950_, v___x_5951_, v_e_5946_);
        return v___x_5952_;
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_mkLetDecls___boxed(
    mut v_decls_5953_: *mut leanh::LeanObject,
    mut v_e_5954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5955_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_decls_5953_, v_e_5954_);
    leanh::lean_dec_ref(v_decls_5953_);
    return v_res_5955_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(
    mut v_fvarId_5956_: *mut leanh::LeanObject,
    mut v_sz_5957_: usize,
    mut v_i_5958_: usize,
    mut v_bs_5959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5960_: u8 = 0;
    let mut v_v_5961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: usize = 0;
    let mut v___x_5968_: usize = 0;
    let mut v___x_5969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: u8 = 0;
    let mut v___x_5974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5975_: u8 = 0;
    let mut v___x_5977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5979_: u8 = 0;
    let mut v_unused_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5960_ = lean_usize_dec_lt(v_i_5958_, v_sz_5957_);
                if v___x_5960_ == 0 {
                    return v_bs_5959_;
                } else {
                    v_v_5961_ = lean_array_uget(v_bs_5959_, v_i_5958_);
                    v_decl_5962_ = leanh::lean_ctor_get(v_v_5961_, 0);
                    v___x_5963_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5964_ = lean_array_uset(v_bs_5959_, v_i_5958_, v___x_5963_);
                    v___x_5971_ = l_Lean_LocalDecl_fvarId(v_decl_5962_);
                    v___x_5972_ = l_Lean_instBEqFVarId_beq(v___x_5971_, v_fvarId_5956_);
                    leanh::lean_dec(v___x_5971_);
                    if v___x_5972_ == 0 {
                        v___y_5966_ = v_v_5961_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_decl_5962_);
                        v_isSharedCheck_5979_ = (!leanh::lean_is_exclusive(v_v_5961_)) as u8;
                        if v_isSharedCheck_5979_ == 0 {
                            v_unused_5980_ = leanh::lean_ctor_get(v_v_5961_, 0);
                            leanh::lean_dec(v_unused_5980_);
                            v___x_5974_ = v_v_5961_;
                            v_isShared_5975_ = v_isSharedCheck_5979_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v_v_5961_);
                            v___x_5974_ = leanh::lean_box(0);
                            v_isShared_5975_ = v_isSharedCheck_5979_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5967_ = 1usize;
                v___x_5968_ = lean_usize_add(v_i_5958_, v___x_5967_);
                v___x_5969_ = lean_array_uset(v_bs_x27_5964_, v_i_5958_, v___y_5966_);
                v_i_5958_ = v___x_5968_;
                v_bs_5959_ = v___x_5969_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_5975_ == 0 {
                    v___x_5977_ = v___x_5974_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5978_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5978_, 0, v_decl_5962_);
                    v___x_5977_ = v_reuseFailAlloc_5978_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_ctor_set_uint8(
                    v___x_5977_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_5972_,
                );
                v___y_5966_ = v___x_5977_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0___boxed(
    mut v_fvarId_5981_: *mut leanh::LeanObject,
    mut v_sz_5982_: *mut leanh::LeanObject,
    mut v_i_5983_: *mut leanh::LeanObject,
    mut v_bs_5984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5985_: usize = 0;
    let mut v_i_boxed_5986_: usize = 0;
    let mut v_res_5987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5985_ = leanh::lean_unbox_usize(v_sz_5982_);
    leanh::lean_dec(v_sz_5982_);
    v_i_boxed_5986_ = leanh::lean_unbox_usize(v_i_5983_);
    leanh::lean_dec(v_i_5983_);
    v_res_5987_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(v_fvarId_5981_, v_sz_boxed_5985_, v_i_boxed_5986_, v_bs_5984_);
    leanh::lean_dec(v_fvarId_5981_);
    return v_res_5987_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_ensureIsLet___redArg(
    mut v_fvarId_5988_: *mut leanh::LeanObject,
    mut v_a_5989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_givenNames_5992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_5993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_valueMap_5994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5997_: u8 = 0;
    let mut v_sz_5998_: usize = 0;
    let mut v___x_5999_: usize = 0;
    let mut v___x_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6007_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5991_ = lean_st_ref_take(v_a_5989_);
                v_givenNames_5992_ = leanh::lean_ctor_get(v___x_5991_, 0);
                v_decls_5993_ = leanh::lean_ctor_get(v___x_5991_, 1);
                v_valueMap_5994_ = leanh::lean_ctor_get(v___x_5991_, 2);
                v_isSharedCheck_6007_ = (!leanh::lean_is_exclusive(v___x_5991_)) as u8;
                if v_isSharedCheck_6007_ == 0 {
                    v___x_5996_ = v___x_5991_;
                    v_isShared_5997_ = v_isSharedCheck_6007_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_valueMap_5994_);
                    leanh::lean_inc(v_decls_5993_);
                    leanh::lean_inc(v_givenNames_5992_);
                    leanh::lean_dec(v___x_5991_);
                    v___x_5996_ = leanh::lean_box(0);
                    v_isShared_5997_ = v_isSharedCheck_6007_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_sz_5998_ = lean_array_size(v_decls_5993_);
                v___x_5999_ = 0usize;
                v___x_6000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_ensureIsLet_spec__0(v_fvarId_5988_, v_sz_5998_, v___x_5999_, v_decls_5993_);
                if v_isShared_5997_ == 0 {
                    leanh::lean_ctor_set(v___x_5996_, 1, v___x_6000_);
                    v___x_6002_ = v___x_5996_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6006_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6006_, 0, v_givenNames_5992_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6006_, 1, v___x_6000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6006_, 2, v_valueMap_5994_);
                    v___x_6002_ = v_reuseFailAlloc_6006_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6003_ = lean_st_ref_set(v_a_5989_, v___x_6002_);
                v___x_6004_ = leanh::lean_box(0);
                v___x_6005_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6005_, 0, v___x_6004_);
                return v___x_6005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_ensureIsLet___redArg___boxed(
    mut v_fvarId_6008_: *mut leanh::LeanObject,
    mut v_a_6009_: *mut leanh::LeanObject,
    mut v_a_6010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6011_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_fvarId_6008_, v_a_6009_);
    leanh::lean_dec(v_a_6009_);
    leanh::lean_dec(v_fvarId_6008_);
    return v_res_6011_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_ensureIsLet(
    mut v_fvarId_6012_: *mut leanh::LeanObject,
    mut v_a_6013_: *mut leanh::LeanObject,
    mut v_a_6014_: *mut leanh::LeanObject,
    mut v_a_6015_: *mut leanh::LeanObject,
    mut v_a_6016_: *mut leanh::LeanObject,
    mut v_a_6017_: *mut leanh::LeanObject,
    mut v_a_6018_: *mut leanh::LeanObject,
    mut v_a_6019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6021_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(v_fvarId_6012_, v_a_6015_);
    return v___x_6021_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_ensureIsLet___boxed(
    mut v_fvarId_6022_: *mut leanh::LeanObject,
    mut v_a_6023_: *mut leanh::LeanObject,
    mut v_a_6024_: *mut leanh::LeanObject,
    mut v_a_6025_: *mut leanh::LeanObject,
    mut v_a_6026_: *mut leanh::LeanObject,
    mut v_a_6027_: *mut leanh::LeanObject,
    mut v_a_6028_: *mut leanh::LeanObject,
    mut v_a_6029_: *mut leanh::LeanObject,
    mut v_a_6030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6031_ = l_Lean_Meta_ExtractLets_ensureIsLet(
        v_fvarId_6022_,
        v_a_6023_,
        v_a_6024_,
        v_a_6025_,
        v_a_6026_,
        v_a_6027_,
        v_a_6028_,
        v_a_6029_,
    );
    leanh::lean_dec(v_a_6029_);
    leanh::lean_dec_ref(v_a_6028_);
    leanh::lean_dec(v_a_6027_);
    leanh::lean_dec_ref(v_a_6026_);
    leanh::lean_dec(v_a_6025_);
    leanh::lean_dec(v_a_6024_);
    leanh::lean_dec_ref(v_a_6023_);
    leanh::lean_dec(v_fvarId_6022_);
    return v_res_6031_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(
    mut v_sz_6032_: usize,
    mut v_i_6033_: usize,
    mut v_bs_6034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6035_: u8 = 0;
    let mut v_v_6036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_6037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: usize = 0;
    let mut v___x_6041_: usize = 0;
    let mut v___x_6042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6035_ = lean_usize_dec_lt(v_i_6033_, v_sz_6032_);
                if v___x_6035_ == 0 {
                    return v_bs_6034_;
                } else {
                    v_v_6036_ = lean_array_uget_borrowed(v_bs_6034_, v_i_6033_);
                    v_decl_6037_ = leanh::lean_ctor_get(v_v_6036_, 0);
                    leanh::lean_inc_ref(v_decl_6037_);
                    v___x_6038_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_6039_ = lean_array_uset(v_bs_6034_, v_i_6033_, v___x_6038_);
                    v___x_6040_ = 1usize;
                    v___x_6041_ = lean_usize_add(v_i_6033_, v___x_6040_);
                    v___x_6042_ = lean_array_uset(v_bs_x27_6039_, v_i_6033_, v_decl_6037_);
                    v_i_6033_ = v___x_6041_;
                    v_bs_6034_ = v___x_6042_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1___boxed(
    mut v_sz_6044_: *mut leanh::LeanObject,
    mut v_i_6045_: *mut leanh::LeanObject,
    mut v_bs_6046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6047_: usize = 0;
    let mut v_i_boxed_6048_: usize = 0;
    let mut v_res_6049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6047_ = leanh::lean_unbox_usize(v_sz_6044_);
    leanh::lean_dec(v_sz_6044_);
    v_i_boxed_6048_ = leanh::lean_unbox_usize(v_i_6045_);
    leanh::lean_dec(v_i_6045_);
    v_res_6049_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_boxed_6047_, v_i_boxed_6048_, v_bs_6046_);
    return v_res_6049_;
}
pub unsafe fn l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0(
    mut v_x_6050_: *mut leanh::LeanObject,
    mut v___y_6051_: *mut leanh::LeanObject,
    mut v___y_6052_: *mut leanh::LeanObject,
    mut v___y_6053_: *mut leanh::LeanObject,
    mut v___y_6054_: *mut leanh::LeanObject,
    mut v___y_6055_: *mut leanh::LeanObject,
    mut v___y_6056_: *mut leanh::LeanObject,
    mut v___y_6057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6059_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_6053_);
    leanh::lean_inc(v___y_6052_);
    leanh::lean_inc_ref(v___y_6051_);
    v___x_6059_ = leanh::lean_apply_8(
        v_x_6050_,
        v___y_6051_,
        v___y_6052_,
        v___y_6053_,
        v___y_6054_,
        v___y_6055_,
        v___y_6056_,
        v___y_6057_,
        leanh::lean_box(0),
    );
    return v___x_6059_;
}
pub unsafe fn l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0___boxed(
    mut v_x_6060_: *mut leanh::LeanObject,
    mut v___y_6061_: *mut leanh::LeanObject,
    mut v___y_6062_: *mut leanh::LeanObject,
    mut v___y_6063_: *mut leanh::LeanObject,
    mut v___y_6064_: *mut leanh::LeanObject,
    mut v___y_6065_: *mut leanh::LeanObject,
    mut v___y_6066_: *mut leanh::LeanObject,
    mut v___y_6067_: *mut leanh::LeanObject,
    mut v___y_6068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6069_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0(v_x_6060_, v___y_6061_, v___y_6062_, v___y_6063_, v___y_6064_, v___y_6065_, v___y_6066_, v___y_6067_);
    leanh::lean_dec(v___y_6063_);
    leanh::lean_dec(v___y_6062_);
    leanh::lean_dec_ref(v___y_6061_);
    return v_res_6069_;
}
pub unsafe fn l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(
    mut v_decls_6070_: *mut leanh::LeanObject,
    mut v_x_6071_: *mut leanh::LeanObject,
    mut v___y_6072_: *mut leanh::LeanObject,
    mut v___y_6073_: *mut leanh::LeanObject,
    mut v___y_6074_: *mut leanh::LeanObject,
    mut v___y_6075_: *mut leanh::LeanObject,
    mut v___y_6076_: *mut leanh::LeanObject,
    mut v___y_6077_: *mut leanh::LeanObject,
    mut v___y_6078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6085_: u8 = 0;
    let mut v___x_6087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6089_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_6074_);
                leanh::lean_inc(v___y_6073_);
                leanh::lean_inc_ref(v___y_6072_);
                v___f_6080_ = leanh::lean_alloc_closure(l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 4);
                leanh::lean_closure_set(v___f_6080_, 0, v_x_6071_);
                leanh::lean_closure_set(v___f_6080_, 1, v___y_6072_);
                leanh::lean_closure_set(v___f_6080_, 2, v___y_6073_);
                leanh::lean_closure_set(v___f_6080_, 3, v___y_6074_);
                v___x_6081_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(
                    leanh::lean_box(0),
                    v_decls_6070_,
                    v___f_6080_,
                    v___y_6075_,
                    v___y_6076_,
                    v___y_6077_,
                    v___y_6078_,
                );
                if leanh::lean_obj_tag(v___x_6081_) == 0 {
                    return v___x_6081_;
                } else {
                    v_a_6082_ = leanh::lean_ctor_get(v___x_6081_, 0);
                    v_isSharedCheck_6089_ = (!leanh::lean_is_exclusive(v___x_6081_)) as u8;
                    if v_isSharedCheck_6089_ == 0 {
                        v___x_6084_ = v___x_6081_;
                        v_isShared_6085_ = v_isSharedCheck_6089_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6082_);
                        leanh::lean_dec(v___x_6081_);
                        v___x_6084_ = leanh::lean_box(0);
                        v_isShared_6085_ = v_isSharedCheck_6089_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6085_ == 0 {
                    v___x_6087_ = v___x_6084_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6088_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6088_, 0, v_a_6082_);
                    v___x_6087_ = v_reuseFailAlloc_6088_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6087_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg___boxed(
    mut v_decls_6090_: *mut leanh::LeanObject,
    mut v_x_6091_: *mut leanh::LeanObject,
    mut v___y_6092_: *mut leanh::LeanObject,
    mut v___y_6093_: *mut leanh::LeanObject,
    mut v___y_6094_: *mut leanh::LeanObject,
    mut v___y_6095_: *mut leanh::LeanObject,
    mut v___y_6096_: *mut leanh::LeanObject,
    mut v___y_6097_: *mut leanh::LeanObject,
    mut v___y_6098_: *mut leanh::LeanObject,
    mut v___y_6099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6100_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v_decls_6090_, v_x_6091_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_, v___y_6096_, v___y_6097_, v___y_6098_);
    leanh::lean_dec(v___y_6098_);
    leanh::lean_dec_ref(v___y_6097_);
    leanh::lean_dec(v___y_6096_);
    leanh::lean_dec_ref(v___y_6095_);
    leanh::lean_dec(v___y_6094_);
    leanh::lean_dec(v___y_6093_);
    leanh::lean_dec_ref(v___y_6092_);
    return v_res_6100_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(
    mut v___x_6101_: *mut leanh::LeanObject,
    mut v_as_6102_: *mut leanh::LeanObject,
    mut v_i_6103_: usize,
    mut v_stop_6104_: usize,
    mut v_b_6105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: usize = 0;
    let mut v___x_6109_: usize = 0;
    let mut v___x_6111_: u8 = 0;
    let mut v___x_6112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_6113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: u8 = 0;
    let mut v___x_6116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6111_ = lean_usize_dec_eq(v_i_6103_, v_stop_6104_);
                if v___x_6111_ == 0 {
                    v___x_6112_ = lean_array_uget_borrowed(v_as_6102_, v_i_6103_);
                    v_decl_6113_ = leanh::lean_ctor_get(v___x_6112_, 0);
                    v___x_6114_ = l_Lean_LocalDecl_fvarId(v_decl_6113_);
                    v___x_6115_ = l_Lean_LocalContext_contains(v___x_6101_, v___x_6114_);
                    leanh::lean_dec(v___x_6114_);
                    if v___x_6115_ == 0 {
                        leanh::lean_inc(v___x_6112_);
                        v___x_6116_ = lean_array_push(v_b_6105_, v___x_6112_);
                        v___y_6107_ = v___x_6116_;
                        state = 1;
                        continue;
                    } else {
                        v___y_6107_ = v_b_6105_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_6105_;
                }
            }
            1 => {
                v___x_6108_ = 1usize;
                v___x_6109_ = lean_usize_add(v_i_6103_, v___x_6108_);
                v_i_6103_ = v___x_6109_;
                v_b_6105_ = v___y_6107_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3___boxed(
    mut v___x_6117_: *mut leanh::LeanObject,
    mut v_as_6118_: *mut leanh::LeanObject,
    mut v_i_6119_: *mut leanh::LeanObject,
    mut v_stop_6120_: *mut leanh::LeanObject,
    mut v_b_6121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6122_: usize = 0;
    let mut v_stop_boxed_6123_: usize = 0;
    let mut v_res_6124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6122_ = leanh::lean_unbox_usize(v_i_6119_);
    leanh::lean_dec(v_i_6119_);
    v_stop_boxed_6123_ = leanh::lean_unbox_usize(v_stop_6120_);
    leanh::lean_dec(v_stop_6120_);
    v_res_6124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v___x_6117_, v_as_6118_, v_i_boxed_6122_, v_stop_boxed_6123_, v_b_6121_);
    leanh::lean_dec_ref(v_as_6118_);
    leanh::lean_dec_ref(v___x_6117_);
    return v_res_6124_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(
    mut v_decls_6125_: *mut leanh::LeanObject,
    mut v_k_6126_: *mut leanh::LeanObject,
    mut v___y_6127_: *mut leanh::LeanObject,
    mut v___y_6128_: *mut leanh::LeanObject,
    mut v___y_6129_: *mut leanh::LeanObject,
    mut v___y_6130_: *mut leanh::LeanObject,
    mut v___y_6131_: *mut leanh::LeanObject,
    mut v___y_6132_: *mut leanh::LeanObject,
    mut v___y_6133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6137_: usize = 0;
    let mut v___x_6138_: usize = 0;
    let mut v_decls_6139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: u8 = 0;
    let mut v___x_6147_: u8 = 0;
    let mut v___x_6148_: usize = 0;
    let mut v___x_6149_: usize = 0;
    let mut v___x_6150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: usize = 0;
    let mut v___x_6152_: usize = 0;
    let mut v___x_6153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_6142_ = leanh::lean_ctor_get(v___y_6130_, 2);
                v___x_6143_ = leanh::lean_unsigned_to_nat(0);
                v___x_6144_ = lean_array_get_size(v_decls_6125_);
                v___x_6145_ = l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0;
                v___x_6146_ = lean_nat_dec_lt(v___x_6143_, v___x_6144_);
                if v___x_6146_ == 0 {
                    v___y_6136_ = v___x_6145_;
                    state = 1;
                    continue;
                } else {
                    v___x_6147_ = lean_nat_dec_le(v___x_6144_, v___x_6144_);
                    if v___x_6147_ == 0 {
                        if v___x_6146_ == 0 {
                            v___y_6136_ = v___x_6145_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6148_ = 0usize;
                            v___x_6149_ = lean_usize_of_nat(v___x_6144_);
                            v___x_6150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v_lctx_6142_, v_decls_6125_, v___x_6148_, v___x_6149_, v___x_6145_);
                            v___y_6136_ = v___x_6150_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_6151_ = 0usize;
                        v___x_6152_ = lean_usize_of_nat(v___x_6144_);
                        v___x_6153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__3(v_lctx_6142_, v_decls_6125_, v___x_6151_, v___x_6152_, v___x_6145_);
                        v___y_6136_ = v___x_6153_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_6137_ = lean_array_size(v___y_6136_);
                v___x_6138_ = 0usize;
                v_decls_6139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_6137_, v___x_6138_, v___y_6136_);
                v___x_6140_ = lean_array_to_list(v_decls_6139_);
                v___x_6141_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v___x_6140_, v_k_6126_, v___y_6127_, v___y_6128_, v___y_6129_, v___y_6130_, v___y_6131_, v___y_6132_, v___y_6133_);
                return v___x_6141_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg___boxed(
    mut v_decls_6154_: *mut leanh::LeanObject,
    mut v_k_6155_: *mut leanh::LeanObject,
    mut v___y_6156_: *mut leanh::LeanObject,
    mut v___y_6157_: *mut leanh::LeanObject,
    mut v___y_6158_: *mut leanh::LeanObject,
    mut v___y_6159_: *mut leanh::LeanObject,
    mut v___y_6160_: *mut leanh::LeanObject,
    mut v___y_6161_: *mut leanh::LeanObject,
    mut v___y_6162_: *mut leanh::LeanObject,
    mut v___y_6163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6164_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v_decls_6154_, v_k_6155_, v___y_6156_, v___y_6157_, v___y_6158_, v___y_6159_, v___y_6160_, v___y_6161_, v___y_6162_);
    leanh::lean_dec(v___y_6162_);
    leanh::lean_dec_ref(v___y_6161_);
    leanh::lean_dec(v___y_6160_);
    leanh::lean_dec_ref(v___y_6159_);
    leanh::lean_dec(v___y_6158_);
    leanh::lean_dec(v___y_6157_);
    leanh::lean_dec_ref(v___y_6156_);
    leanh::lean_dec_ref(v_decls_6154_);
    return v_res_6164_;
}
pub unsafe fn l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(
    mut v_fvarId_6165_: *mut leanh::LeanObject,
    mut v_as_6166_: *mut leanh::LeanObject,
    mut v_j_6167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: u8 = 0;
    let mut v___x_6170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: u8 = 0;
    let mut v___x_6175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6168_ = lean_array_get_size(v_as_6166_);
                v___x_6169_ = lean_nat_dec_lt(v_j_6167_, v___x_6168_);
                if v___x_6169_ == 0 {
                    leanh::lean_dec(v_j_6167_);
                    v___x_6170_ = leanh::lean_box(0);
                    return v___x_6170_;
                } else {
                    v___x_6171_ = lean_array_fget_borrowed(v_as_6166_, v_j_6167_);
                    v_decl_6172_ = leanh::lean_ctor_get(v___x_6171_, 0);
                    v___x_6173_ = l_Lean_LocalDecl_fvarId(v_decl_6172_);
                    v___x_6174_ = l_Lean_instBEqFVarId_beq(v___x_6173_, v_fvarId_6165_);
                    leanh::lean_dec(v___x_6173_);
                    if v___x_6174_ == 0 {
                        v___x_6175_ = leanh::lean_unsigned_to_nat(1);
                        v___x_6176_ = lean_nat_add(v_j_6167_, v___x_6175_);
                        leanh::lean_dec(v_j_6167_);
                        v_j_6167_ = v___x_6176_;
                        state = 0;
                        continue;
                    } else {
                        v___x_6178_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_6178_, 0, v_j_6167_);
                        return v___x_6178_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0___boxed(
    mut v_fvarId_6179_: *mut leanh::LeanObject,
    mut v_as_6180_: *mut leanh::LeanObject,
    mut v_j_6181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6182_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(
        v_fvarId_6179_,
        v_as_6180_,
        v_j_6181_,
    );
    leanh::lean_dec_ref(v_as_6180_);
    leanh::lean_dec(v_fvarId_6179_);
    return v_res_6182_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_withDeclInContext___redArg(
    mut v_fvarId_6183_: *mut leanh::LeanObject,
    mut v_k_6184_: *mut leanh::LeanObject,
    mut v_a_6185_: *mut leanh::LeanObject,
    mut v_a_6186_: *mut leanh::LeanObject,
    mut v_a_6187_: *mut leanh::LeanObject,
    mut v_a_6188_: *mut leanh::LeanObject,
    mut v_a_6189_: *mut leanh::LeanObject,
    mut v_a_6190_: *mut leanh::LeanObject,
    mut v_a_6191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: u8 = 0;
    v___x_6193_ = lean_st_ref_get(v_a_6187_);
    v_lctx_6194_ = leanh::lean_ctor_get(v_a_6188_, 2);
    v___x_6195_ = l_Lean_LocalContext_contains(v_lctx_6194_, v_fvarId_6183_);
    if v___x_6195_ == 0 {
        let mut v_decls_6196_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6197_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6198_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_decls_6196_ = leanh::lean_ctor_get(v___x_6193_, 1);
        leanh::lean_inc_ref(v_decls_6196_);
        leanh::lean_dec(v___x_6193_);
        v___x_6197_ = leanh::lean_unsigned_to_nat(0);
        v___x_6198_ =
            l_Array_findIdx_x3f_loop___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__0(
                v_fvarId_6183_,
                v_decls_6196_,
                v___x_6197_,
            );
        if leanh::lean_obj_tag(v___x_6198_) == 1 {
            let mut v_val_6199_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6200_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6201_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6203_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6204_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_6199_ = leanh::lean_ctor_get(v___x_6198_, 0);
            leanh::lean_inc(v_val_6199_);
            leanh::lean_dec_ref_known(v___x_6198_, 1);
            v___x_6200_ = leanh::lean_unsigned_to_nat(1);
            v___x_6201_ = lean_nat_add(v_val_6199_, v___x_6200_);
            leanh::lean_dec(v_val_6199_);
            v___x_6202_ = l_Array_toSubarray___redArg(v_decls_6196_, v___x_6197_, v___x_6201_);
            v___x_6203_ = l_Subarray_copy___redArg(v___x_6202_);
            v___x_6204_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v___x_6203_, v_k_6184_, v_a_6185_, v_a_6186_, v_a_6187_, v_a_6188_, v_a_6189_, v_a_6190_, v_a_6191_);
            leanh::lean_dec_ref(v___x_6203_);
            return v___x_6204_;
        } else {
            let mut v___x_6205_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_6198_);
            leanh::lean_dec_ref(v_decls_6196_);
            leanh::lean_inc(v_a_6191_);
            leanh::lean_inc_ref(v_a_6190_);
            leanh::lean_inc(v_a_6189_);
            leanh::lean_inc_ref(v_a_6188_);
            leanh::lean_inc(v_a_6187_);
            leanh::lean_inc(v_a_6186_);
            leanh::lean_inc_ref(v_a_6185_);
            v___x_6205_ = leanh::lean_apply_8(
                v_k_6184_,
                v_a_6185_,
                v_a_6186_,
                v_a_6187_,
                v_a_6188_,
                v_a_6189_,
                v_a_6190_,
                v_a_6191_,
                leanh::lean_box(0),
            );
            return v___x_6205_;
        }
    } else {
        let mut v___x_6206_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_6193_);
        leanh::lean_inc(v_a_6191_);
        leanh::lean_inc_ref(v_a_6190_);
        leanh::lean_inc(v_a_6189_);
        leanh::lean_inc_ref(v_a_6188_);
        leanh::lean_inc(v_a_6187_);
        leanh::lean_inc(v_a_6186_);
        leanh::lean_inc_ref(v_a_6185_);
        v___x_6206_ = leanh::lean_apply_8(
            v_k_6184_,
            v_a_6185_,
            v_a_6186_,
            v_a_6187_,
            v_a_6188_,
            v_a_6189_,
            v_a_6190_,
            v_a_6191_,
            leanh::lean_box(0),
        );
        return v___x_6206_;
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_withDeclInContext___redArg___boxed(
    mut v_fvarId_6207_: *mut leanh::LeanObject,
    mut v_k_6208_: *mut leanh::LeanObject,
    mut v_a_6209_: *mut leanh::LeanObject,
    mut v_a_6210_: *mut leanh::LeanObject,
    mut v_a_6211_: *mut leanh::LeanObject,
    mut v_a_6212_: *mut leanh::LeanObject,
    mut v_a_6213_: *mut leanh::LeanObject,
    mut v_a_6214_: *mut leanh::LeanObject,
    mut v_a_6215_: *mut leanh::LeanObject,
    mut v_a_6216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6217_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(
        v_fvarId_6207_,
        v_k_6208_,
        v_a_6209_,
        v_a_6210_,
        v_a_6211_,
        v_a_6212_,
        v_a_6213_,
        v_a_6214_,
        v_a_6215_,
    );
    leanh::lean_dec(v_a_6215_);
    leanh::lean_dec_ref(v_a_6214_);
    leanh::lean_dec(v_a_6213_);
    leanh::lean_dec_ref(v_a_6212_);
    leanh::lean_dec(v_a_6211_);
    leanh::lean_dec(v_a_6210_);
    leanh::lean_dec_ref(v_a_6209_);
    leanh::lean_dec(v_fvarId_6207_);
    return v_res_6217_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_withDeclInContext(
    mut v_00_u03b1_6218_: *mut leanh::LeanObject,
    mut v_fvarId_6219_: *mut leanh::LeanObject,
    mut v_k_6220_: *mut leanh::LeanObject,
    mut v_a_6221_: *mut leanh::LeanObject,
    mut v_a_6222_: *mut leanh::LeanObject,
    mut v_a_6223_: *mut leanh::LeanObject,
    mut v_a_6224_: *mut leanh::LeanObject,
    mut v_a_6225_: *mut leanh::LeanObject,
    mut v_a_6226_: *mut leanh::LeanObject,
    mut v_a_6227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6229_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(
        v_fvarId_6219_,
        v_k_6220_,
        v_a_6221_,
        v_a_6222_,
        v_a_6223_,
        v_a_6224_,
        v_a_6225_,
        v_a_6226_,
        v_a_6227_,
    );
    return v___x_6229_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_withDeclInContext___boxed(
    mut v_00_u03b1_6230_: *mut leanh::LeanObject,
    mut v_fvarId_6231_: *mut leanh::LeanObject,
    mut v_k_6232_: *mut leanh::LeanObject,
    mut v_a_6233_: *mut leanh::LeanObject,
    mut v_a_6234_: *mut leanh::LeanObject,
    mut v_a_6235_: *mut leanh::LeanObject,
    mut v_a_6236_: *mut leanh::LeanObject,
    mut v_a_6237_: *mut leanh::LeanObject,
    mut v_a_6238_: *mut leanh::LeanObject,
    mut v_a_6239_: *mut leanh::LeanObject,
    mut v_a_6240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6241_ = l_Lean_Meta_ExtractLets_withDeclInContext(
        v_00_u03b1_6230_,
        v_fvarId_6231_,
        v_k_6232_,
        v_a_6233_,
        v_a_6234_,
        v_a_6235_,
        v_a_6236_,
        v_a_6237_,
        v_a_6238_,
        v_a_6239_,
    );
    leanh::lean_dec(v_a_6239_);
    leanh::lean_dec_ref(v_a_6238_);
    leanh::lean_dec(v_a_6237_);
    leanh::lean_dec_ref(v_a_6236_);
    leanh::lean_dec(v_a_6235_);
    leanh::lean_dec(v_a_6234_);
    leanh::lean_dec_ref(v_a_6233_);
    leanh::lean_dec(v_fvarId_6231_);
    return v_res_6241_;
}
pub unsafe fn l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2(
    mut v_00_u03b1_6242_: *mut leanh::LeanObject,
    mut v_decls_6243_: *mut leanh::LeanObject,
    mut v_x_6244_: *mut leanh::LeanObject,
    mut v___y_6245_: *mut leanh::LeanObject,
    mut v___y_6246_: *mut leanh::LeanObject,
    mut v___y_6247_: *mut leanh::LeanObject,
    mut v___y_6248_: *mut leanh::LeanObject,
    mut v___y_6249_: *mut leanh::LeanObject,
    mut v___y_6250_: *mut leanh::LeanObject,
    mut v___y_6251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6253_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___redArg(v_decls_6243_, v_x_6244_, v___y_6245_, v___y_6246_, v___y_6247_, v___y_6248_, v___y_6249_, v___y_6250_, v___y_6251_);
    return v___x_6253_;
}
pub unsafe fn l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2___boxed(
    mut v_00_u03b1_6254_: *mut leanh::LeanObject,
    mut v_decls_6255_: *mut leanh::LeanObject,
    mut v_x_6256_: *mut leanh::LeanObject,
    mut v___y_6257_: *mut leanh::LeanObject,
    mut v___y_6258_: *mut leanh::LeanObject,
    mut v___y_6259_: *mut leanh::LeanObject,
    mut v___y_6260_: *mut leanh::LeanObject,
    mut v___y_6261_: *mut leanh::LeanObject,
    mut v___y_6262_: *mut leanh::LeanObject,
    mut v___y_6263_: *mut leanh::LeanObject,
    mut v___y_6264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6265_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__2(v_00_u03b1_6254_, v_decls_6255_, v_x_6256_, v___y_6257_, v___y_6258_, v___y_6259_, v___y_6260_, v___y_6261_, v___y_6262_, v___y_6263_);
    leanh::lean_dec(v___y_6263_);
    leanh::lean_dec_ref(v___y_6262_);
    leanh::lean_dec(v___y_6261_);
    leanh::lean_dec_ref(v___y_6260_);
    leanh::lean_dec(v___y_6259_);
    leanh::lean_dec(v___y_6258_);
    leanh::lean_dec_ref(v___y_6257_);
    return v_res_6265_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1(
    mut v_00_u03b1_6266_: *mut leanh::LeanObject,
    mut v_decls_6267_: *mut leanh::LeanObject,
    mut v_k_6268_: *mut leanh::LeanObject,
    mut v___y_6269_: *mut leanh::LeanObject,
    mut v___y_6270_: *mut leanh::LeanObject,
    mut v___y_6271_: *mut leanh::LeanObject,
    mut v___y_6272_: *mut leanh::LeanObject,
    mut v___y_6273_: *mut leanh::LeanObject,
    mut v___y_6274_: *mut leanh::LeanObject,
    mut v___y_6275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6277_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___redArg(v_decls_6267_, v_k_6268_, v___y_6269_, v___y_6270_, v___y_6271_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_);
    return v___x_6277_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1___boxed(
    mut v_00_u03b1_6278_: *mut leanh::LeanObject,
    mut v_decls_6279_: *mut leanh::LeanObject,
    mut v_k_6280_: *mut leanh::LeanObject,
    mut v___y_6281_: *mut leanh::LeanObject,
    mut v___y_6282_: *mut leanh::LeanObject,
    mut v___y_6283_: *mut leanh::LeanObject,
    mut v___y_6284_: *mut leanh::LeanObject,
    mut v___y_6285_: *mut leanh::LeanObject,
    mut v___y_6286_: *mut leanh::LeanObject,
    mut v___y_6287_: *mut leanh::LeanObject,
    mut v___y_6288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6289_ = l_Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1(v_00_u03b1_6278_, v_decls_6279_, v_k_6280_, v___y_6281_, v___y_6282_, v___y_6283_, v___y_6284_, v___y_6285_, v___y_6286_, v___y_6287_);
    leanh::lean_dec(v___y_6287_);
    leanh::lean_dec_ref(v___y_6286_);
    leanh::lean_dec(v___y_6285_);
    leanh::lean_dec_ref(v___y_6284_);
    leanh::lean_dec(v___y_6283_);
    leanh::lean_dec(v___y_6282_);
    leanh::lean_dec_ref(v___y_6281_);
    leanh::lean_dec_ref(v_decls_6279_);
    return v_res_6289_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(
    mut v_e_6290_: *mut leanh::LeanObject,
    mut v___y_6291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6293_: u8 = 0;
    let mut v___x_6294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6307_: u8 = 0;
    let mut v___x_6309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6313_: u8 = 0;
    let mut v_unused_6314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6293_ = l_Lean_Expr_hasMVar(v_e_6290_);
                if v___x_6293_ == 0 {
                    v___x_6294_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6294_, 0, v_e_6290_);
                    return v___x_6294_;
                } else {
                    v___x_6295_ = lean_st_ref_get(v___y_6291_);
                    v_mctx_6296_ = leanh::lean_ctor_get(v___x_6295_, 0);
                    leanh::lean_inc_ref(v_mctx_6296_);
                    leanh::lean_dec(v___x_6295_);
                    v___x_6297_ = l_Lean_instantiateMVarsCore(v_mctx_6296_, v_e_6290_);
                    v_fst_6298_ = leanh::lean_ctor_get(v___x_6297_, 0);
                    leanh::lean_inc(v_fst_6298_);
                    v_snd_6299_ = leanh::lean_ctor_get(v___x_6297_, 1);
                    leanh::lean_inc(v_snd_6299_);
                    leanh::lean_dec_ref(v___x_6297_);
                    v___x_6300_ = lean_st_ref_take(v___y_6291_);
                    v_cache_6301_ = leanh::lean_ctor_get(v___x_6300_, 1);
                    v_zetaDeltaFVarIds_6302_ = leanh::lean_ctor_get(v___x_6300_, 2);
                    v_postponed_6303_ = leanh::lean_ctor_get(v___x_6300_, 3);
                    v_diag_6304_ = leanh::lean_ctor_get(v___x_6300_, 4);
                    v_isSharedCheck_6313_ = (!leanh::lean_is_exclusive(v___x_6300_)) as u8;
                    if v_isSharedCheck_6313_ == 0 {
                        v_unused_6314_ = leanh::lean_ctor_get(v___x_6300_, 0);
                        leanh::lean_dec(v_unused_6314_);
                        v___x_6306_ = v___x_6300_;
                        v_isShared_6307_ = v_isSharedCheck_6313_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_6304_);
                        leanh::lean_inc(v_postponed_6303_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_6302_);
                        leanh::lean_inc(v_cache_6301_);
                        leanh::lean_dec(v___x_6300_);
                        v___x_6306_ = leanh::lean_box(0);
                        v_isShared_6307_ = v_isSharedCheck_6313_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6307_ == 0 {
                    leanh::lean_ctor_set(v___x_6306_, 0, v_snd_6299_);
                    v___x_6309_ = v___x_6306_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6312_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6312_, 0, v_snd_6299_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6312_, 1, v_cache_6301_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6312_,
                        2,
                        v_zetaDeltaFVarIds_6302_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6312_, 3, v_postponed_6303_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6312_, 4, v_diag_6304_);
                    v___x_6309_ = v_reuseFailAlloc_6312_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6310_ = lean_st_ref_set(v___y_6291_, v___x_6309_);
                v___x_6311_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6311_, 0, v_fst_6298_);
                return v___x_6311_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg___boxed(
    mut v_e_6315_: *mut leanh::LeanObject,
    mut v___y_6316_: *mut leanh::LeanObject,
    mut v___y_6317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6318_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(
            v_e_6315_,
            v___y_6316_,
        );
    leanh::lean_dec(v___y_6316_);
    return v_res_6318_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(
    mut v_e_6319_: *mut leanh::LeanObject,
    mut v___y_6320_: *mut leanh::LeanObject,
    mut v___y_6321_: *mut leanh::LeanObject,
    mut v___y_6322_: *mut leanh::LeanObject,
    mut v___y_6323_: *mut leanh::LeanObject,
    mut v___y_6324_: *mut leanh::LeanObject,
    mut v___y_6325_: *mut leanh::LeanObject,
    mut v___y_6326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6328_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(
            v_e_6319_,
            v___y_6324_,
        );
    return v___x_6328_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___boxed(
    mut v_e_6329_: *mut leanh::LeanObject,
    mut v___y_6330_: *mut leanh::LeanObject,
    mut v___y_6331_: *mut leanh::LeanObject,
    mut v___y_6332_: *mut leanh::LeanObject,
    mut v___y_6333_: *mut leanh::LeanObject,
    mut v___y_6334_: *mut leanh::LeanObject,
    mut v___y_6335_: *mut leanh::LeanObject,
    mut v___y_6336_: *mut leanh::LeanObject,
    mut v___y_6337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6338_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0(
        v_e_6329_,
        v___y_6330_,
        v___y_6331_,
        v___y_6332_,
        v___y_6333_,
        v___y_6334_,
        v___y_6335_,
        v___y_6336_,
    );
    leanh::lean_dec(v___y_6336_);
    leanh::lean_dec_ref(v___y_6335_);
    leanh::lean_dec(v___y_6334_);
    leanh::lean_dec_ref(v___y_6333_);
    leanh::lean_dec(v___y_6332_);
    leanh::lean_dec(v___y_6331_);
    leanh::lean_dec_ref(v___y_6330_);
    return v_res_6338_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(
    mut v_as_6339_: *mut leanh::LeanObject,
    mut v_i_6340_: usize,
    mut v_stop_6341_: usize,
    mut v_b_6342_: *mut leanh::LeanObject,
    mut v___y_6343_: *mut leanh::LeanObject,
    mut v___y_6344_: *mut leanh::LeanObject,
    mut v___y_6345_: *mut leanh::LeanObject,
    mut v___y_6346_: *mut leanh::LeanObject,
    mut v___y_6347_: *mut leanh::LeanObject,
    mut v___y_6348_: *mut leanh::LeanObject,
    mut v___y_6349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_6352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: usize = 0;
    let mut v___x_6354_: usize = 0;
    let mut v___x_6357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: u8 = 0;
    let mut v___x_6359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6363_: u8 = 0;
    let mut v___x_6364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_givenNames_6368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_6369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_valueMap_6370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6373_: u8 = 0;
    let mut v___x_6374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6381_: u8 = 0;
    let mut v_a_6382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6385_: u8 = 0;
    let mut v___x_6387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6389_: u8 = 0;
    let mut v___x_6390_: u8 = 0;
    let mut v___x_6391_: u8 = 0;
    let mut v___x_6392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6358_ = lean_usize_dec_eq(v_i_6340_, v_stop_6341_);
                if v___x_6358_ == 0 {
                    v___x_6359_ = lean_array_uget_borrowed(v_as_6339_, v_i_6340_);
                    if leanh::lean_obj_tag(v___x_6359_) == 0 {
                        v___x_6360_ = leanh::lean_box(0);
                        v_a_6352_ = v___x_6360_;
                        state = 1;
                        continue;
                    } else {
                        v_val_6361_ = leanh::lean_ctor_get(v___x_6359_, 0);
                        v___x_6390_ = l_Lean_LocalDecl_isLet(v_val_6361_, v___x_6358_);
                        if v___x_6390_ == 0 {
                            v___y_6363_ = v___x_6390_;
                            state = 3;
                            continue;
                        } else {
                            v___x_6391_ = l_Lean_LocalDecl_isImplementationDetail(v_val_6361_);
                            if v___x_6391_ == 0 {
                                v___y_6363_ = v___x_6390_;
                                state = 3;
                                continue;
                            } else {
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_6392_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6392_, 0, v_b_6342_);
                    return v___x_6392_;
                }
            }
            1 => {
                v___x_6353_ = 1usize;
                v___x_6354_ = lean_usize_add(v_i_6340_, v___x_6353_);
                v_i_6340_ = v___x_6354_;
                v_b_6342_ = v_a_6352_;
                state = 0;
                continue;
            }
            2 => {
                v___x_6357_ = leanh::lean_box(0);
                v_a_6352_ = v___x_6357_;
                state = 1;
                continue;
            }
            3 => {
                if v___y_6363_ == 0 {
                    state = 2;
                    continue;
                } else {
                    v___x_6364_ = l_Lean_LocalDecl_value(v_val_6361_, v___x_6358_);
                    v___x_6365_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_6364_, v___y_6347_);
                    if leanh::lean_obj_tag(v___x_6365_) == 0 {
                        v_a_6366_ = leanh::lean_ctor_get(v___x_6365_, 0);
                        leanh::lean_inc(v_a_6366_);
                        leanh::lean_dec_ref_known(v___x_6365_, 1);
                        v___x_6367_ = lean_st_ref_take(v___y_6345_);
                        v_givenNames_6368_ = leanh::lean_ctor_get(v___x_6367_, 0);
                        v_decls_6369_ = leanh::lean_ctor_get(v___x_6367_, 1);
                        v_valueMap_6370_ = leanh::lean_ctor_get(v___x_6367_, 2);
                        v_isSharedCheck_6381_ =
                            (!leanh::lean_is_exclusive(v___x_6367_)) as u8;
                        if v_isSharedCheck_6381_ == 0 {
                            v___x_6372_ = v___x_6367_;
                            v_isShared_6373_ = v_isSharedCheck_6381_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_valueMap_6370_);
                            leanh::lean_inc(v_decls_6369_);
                            leanh::lean_inc(v_givenNames_6368_);
                            leanh::lean_dec(v___x_6367_);
                            v___x_6372_ = leanh::lean_box(0);
                            v_isShared_6373_ = v_isSharedCheck_6381_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_6382_ = leanh::lean_ctor_get(v___x_6365_, 0);
                        v_isSharedCheck_6389_ =
                            (!leanh::lean_is_exclusive(v___x_6365_)) as u8;
                        if v_isSharedCheck_6389_ == 0 {
                            v___x_6384_ = v___x_6365_;
                            v_isShared_6385_ = v_isSharedCheck_6389_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6382_);
                            leanh::lean_dec(v___x_6365_);
                            v___x_6384_ = leanh::lean_box(0);
                            v_isShared_6385_ = v_isSharedCheck_6389_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_6374_ = l_Lean_LocalDecl_fvarId(v_val_6361_);
                v___x_6375_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_6370_, v_a_6366_, v___x_6374_);
                if v_isShared_6373_ == 0 {
                    leanh::lean_ctor_set(v___x_6372_, 2, v___x_6375_);
                    v___x_6377_ = v___x_6372_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6380_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6380_, 0, v_givenNames_6368_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6380_, 1, v_decls_6369_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6380_, 2, v___x_6375_);
                    v___x_6377_ = v_reuseFailAlloc_6380_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6378_ = lean_st_ref_set(v___y_6345_, v___x_6377_);
                v___x_6379_ = leanh::lean_box(0);
                v_a_6352_ = v___x_6379_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_6385_ == 0 {
                    v___x_6387_ = v___x_6384_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6388_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6388_, 0, v_a_6382_);
                    v___x_6387_ = v_reuseFailAlloc_6388_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6___boxed(
    mut v_as_6393_: *mut leanh::LeanObject,
    mut v_i_6394_: *mut leanh::LeanObject,
    mut v_stop_6395_: *mut leanh::LeanObject,
    mut v_b_6396_: *mut leanh::LeanObject,
    mut v___y_6397_: *mut leanh::LeanObject,
    mut v___y_6398_: *mut leanh::LeanObject,
    mut v___y_6399_: *mut leanh::LeanObject,
    mut v___y_6400_: *mut leanh::LeanObject,
    mut v___y_6401_: *mut leanh::LeanObject,
    mut v___y_6402_: *mut leanh::LeanObject,
    mut v___y_6403_: *mut leanh::LeanObject,
    mut v___y_6404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6405_: usize = 0;
    let mut v_stop_boxed_6406_: usize = 0;
    let mut v_res_6407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6405_ = leanh::lean_unbox_usize(v_i_6394_);
    leanh::lean_dec(v_i_6394_);
    v_stop_boxed_6406_ = leanh::lean_unbox_usize(v_stop_6395_);
    leanh::lean_dec(v_stop_6395_);
    v_res_6407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_6393_, v_i_boxed_6405_, v_stop_boxed_6406_, v_b_6396_, v___y_6397_, v___y_6398_, v___y_6399_, v___y_6400_, v___y_6401_, v___y_6402_, v___y_6403_);
    leanh::lean_dec(v___y_6403_);
    leanh::lean_dec_ref(v___y_6402_);
    leanh::lean_dec(v___y_6401_);
    leanh::lean_dec_ref(v___y_6400_);
    leanh::lean_dec(v___y_6399_);
    leanh::lean_dec(v___y_6398_);
    leanh::lean_dec_ref(v___y_6397_);
    leanh::lean_dec_ref(v_as_6393_);
    return v_res_6407_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(
    mut v_as_6408_: *mut leanh::LeanObject,
    mut v_i_6409_: usize,
    mut v_stop_6410_: usize,
    mut v_b_6411_: *mut leanh::LeanObject,
    mut v___y_6412_: *mut leanh::LeanObject,
    mut v___y_6413_: *mut leanh::LeanObject,
    mut v___y_6414_: *mut leanh::LeanObject,
    mut v___y_6415_: *mut leanh::LeanObject,
    mut v___y_6416_: *mut leanh::LeanObject,
    mut v___y_6417_: *mut leanh::LeanObject,
    mut v___y_6418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_6421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: usize = 0;
    let mut v___x_6423_: usize = 0;
    let mut v___x_6424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: u8 = 0;
    let mut v___x_6428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6432_: u8 = 0;
    let mut v___x_6433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_givenNames_6437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_6438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_valueMap_6439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6442_: u8 = 0;
    let mut v___x_6443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6450_: u8 = 0;
    let mut v_a_6451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6454_: u8 = 0;
    let mut v___x_6456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6458_: u8 = 0;
    let mut v___x_6459_: u8 = 0;
    let mut v___x_6460_: u8 = 0;
    let mut v___x_6461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6427_ = lean_usize_dec_eq(v_i_6409_, v_stop_6410_);
                if v___x_6427_ == 0 {
                    v___x_6428_ = lean_array_uget_borrowed(v_as_6408_, v_i_6409_);
                    if leanh::lean_obj_tag(v___x_6428_) == 0 {
                        v___x_6429_ = leanh::lean_box(0);
                        v_a_6421_ = v___x_6429_;
                        state = 1;
                        continue;
                    } else {
                        v_val_6430_ = leanh::lean_ctor_get(v___x_6428_, 0);
                        v___x_6459_ = l_Lean_LocalDecl_isLet(v_val_6430_, v___x_6427_);
                        if v___x_6459_ == 0 {
                            v___y_6432_ = v___x_6459_;
                            state = 3;
                            continue;
                        } else {
                            v___x_6460_ = l_Lean_LocalDecl_isImplementationDetail(v_val_6430_);
                            if v___x_6460_ == 0 {
                                v___y_6432_ = v___x_6459_;
                                state = 3;
                                continue;
                            } else {
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_6461_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6461_, 0, v_b_6411_);
                    return v___x_6461_;
                }
            }
            1 => {
                v___x_6422_ = 1usize;
                v___x_6423_ = lean_usize_add(v_i_6409_, v___x_6422_);
                v___x_6424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3_spec__6(v_as_6408_, v___x_6423_, v_stop_6410_, v_a_6421_, v___y_6412_, v___y_6413_, v___y_6414_, v___y_6415_, v___y_6416_, v___y_6417_, v___y_6418_);
                return v___x_6424_;
            }
            2 => {
                v___x_6426_ = leanh::lean_box(0);
                v_a_6421_ = v___x_6426_;
                state = 1;
                continue;
            }
            3 => {
                if v___y_6432_ == 0 {
                    state = 2;
                    continue;
                } else {
                    v___x_6433_ = l_Lean_LocalDecl_value(v_val_6430_, v___x_6427_);
                    v___x_6434_ = l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(v___x_6433_, v___y_6416_);
                    if leanh::lean_obj_tag(v___x_6434_) == 0 {
                        v_a_6435_ = leanh::lean_ctor_get(v___x_6434_, 0);
                        leanh::lean_inc(v_a_6435_);
                        leanh::lean_dec_ref_known(v___x_6434_, 1);
                        v___x_6436_ = lean_st_ref_take(v___y_6414_);
                        v_givenNames_6437_ = leanh::lean_ctor_get(v___x_6436_, 0);
                        v_decls_6438_ = leanh::lean_ctor_get(v___x_6436_, 1);
                        v_valueMap_6439_ = leanh::lean_ctor_get(v___x_6436_, 2);
                        v_isSharedCheck_6450_ =
                            (!leanh::lean_is_exclusive(v___x_6436_)) as u8;
                        if v_isSharedCheck_6450_ == 0 {
                            v___x_6441_ = v___x_6436_;
                            v_isShared_6442_ = v_isSharedCheck_6450_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_valueMap_6439_);
                            leanh::lean_inc(v_decls_6438_);
                            leanh::lean_inc(v_givenNames_6437_);
                            leanh::lean_dec(v___x_6436_);
                            v___x_6441_ = leanh::lean_box(0);
                            v_isShared_6442_ = v_isSharedCheck_6450_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_6451_ = leanh::lean_ctor_get(v___x_6434_, 0);
                        v_isSharedCheck_6458_ =
                            (!leanh::lean_is_exclusive(v___x_6434_)) as u8;
                        if v_isSharedCheck_6458_ == 0 {
                            v___x_6453_ = v___x_6434_;
                            v_isShared_6454_ = v_isSharedCheck_6458_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6451_);
                            leanh::lean_dec(v___x_6434_);
                            v___x_6453_ = leanh::lean_box(0);
                            v_isShared_6454_ = v_isSharedCheck_6458_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_6443_ = l_Lean_LocalDecl_fvarId(v_val_6430_);
                v___x_6444_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_addDecl_spec__0___redArg(v_valueMap_6439_, v_a_6435_, v___x_6443_);
                if v_isShared_6442_ == 0 {
                    leanh::lean_ctor_set(v___x_6441_, 2, v___x_6444_);
                    v___x_6446_ = v___x_6441_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6449_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6449_, 0, v_givenNames_6437_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6449_, 1, v_decls_6438_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6449_, 2, v___x_6444_);
                    v___x_6446_ = v_reuseFailAlloc_6449_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6447_ = lean_st_ref_set(v___y_6414_, v___x_6446_);
                v___x_6448_ = leanh::lean_box(0);
                v_a_6421_ = v___x_6448_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_6454_ == 0 {
                    v___x_6456_ = v___x_6453_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6457_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6457_, 0, v_a_6451_);
                    v___x_6456_ = v_reuseFailAlloc_6457_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6456_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3___boxed(
    mut v_as_6462_: *mut leanh::LeanObject,
    mut v_i_6463_: *mut leanh::LeanObject,
    mut v_stop_6464_: *mut leanh::LeanObject,
    mut v_b_6465_: *mut leanh::LeanObject,
    mut v___y_6466_: *mut leanh::LeanObject,
    mut v___y_6467_: *mut leanh::LeanObject,
    mut v___y_6468_: *mut leanh::LeanObject,
    mut v___y_6469_: *mut leanh::LeanObject,
    mut v___y_6470_: *mut leanh::LeanObject,
    mut v___y_6471_: *mut leanh::LeanObject,
    mut v___y_6472_: *mut leanh::LeanObject,
    mut v___y_6473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6474_: usize = 0;
    let mut v_stop_boxed_6475_: usize = 0;
    let mut v_res_6476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6474_ = leanh::lean_unbox_usize(v_i_6463_);
    leanh::lean_dec(v_i_6463_);
    v_stop_boxed_6475_ = leanh::lean_unbox_usize(v_stop_6464_);
    leanh::lean_dec(v_stop_6464_);
    v_res_6476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_as_6462_, v_i_boxed_6474_, v_stop_boxed_6475_, v_b_6465_, v___y_6466_, v___y_6467_, v___y_6468_, v___y_6469_, v___y_6470_, v___y_6471_, v___y_6472_);
    leanh::lean_dec(v___y_6472_);
    leanh::lean_dec_ref(v___y_6471_);
    leanh::lean_dec(v___y_6470_);
    leanh::lean_dec_ref(v___y_6469_);
    leanh::lean_dec(v___y_6468_);
    leanh::lean_dec(v___y_6467_);
    leanh::lean_dec_ref(v___y_6466_);
    leanh::lean_dec_ref(v_as_6462_);
    return v_res_6476_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(
    mut v_x_6477_: *mut leanh::LeanObject,
    mut v___y_6478_: *mut leanh::LeanObject,
    mut v___y_6479_: *mut leanh::LeanObject,
    mut v___y_6480_: *mut leanh::LeanObject,
    mut v___y_6481_: *mut leanh::LeanObject,
    mut v___y_6482_: *mut leanh::LeanObject,
    mut v___y_6483_: *mut leanh::LeanObject,
    mut v___y_6484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_6486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6489_: u8 = 0;
    let mut v___x_6490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: u8 = 0;
    let mut v___x_6495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: u8 = 0;
    let mut v___x_6499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: usize = 0;
    let mut v___x_6502_: usize = 0;
    let mut v___x_6503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: usize = 0;
    let mut v___x_6505_: usize = 0;
    let mut v___x_6506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6507_: u8 = 0;
    let mut v_vs_6508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6511_: u8 = 0;
    let mut v___x_6512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: u8 = 0;
    let mut v___x_6517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: u8 = 0;
    let mut v___x_6521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: usize = 0;
    let mut v___x_6524_: usize = 0;
    let mut v___x_6525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: usize = 0;
    let mut v___x_6527_: usize = 0;
    let mut v___x_6528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6529_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6477_) == 0 {
                    v_cs_6486_ = leanh::lean_ctor_get(v_x_6477_, 0);
                    v_isSharedCheck_6507_ = (!leanh::lean_is_exclusive(v_x_6477_)) as u8;
                    if v_isSharedCheck_6507_ == 0 {
                        v___x_6488_ = v_x_6477_;
                        v_isShared_6489_ = v_isSharedCheck_6507_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_cs_6486_);
                        leanh::lean_dec(v_x_6477_);
                        v___x_6488_ = leanh::lean_box(0);
                        v_isShared_6489_ = v_isSharedCheck_6507_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_6508_ = leanh::lean_ctor_get(v_x_6477_, 0);
                    v_isSharedCheck_6529_ = (!leanh::lean_is_exclusive(v_x_6477_)) as u8;
                    if v_isSharedCheck_6529_ == 0 {
                        v___x_6510_ = v_x_6477_;
                        v_isShared_6511_ = v_isSharedCheck_6529_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_6508_);
                        leanh::lean_dec(v_x_6477_);
                        v___x_6510_ = leanh::lean_box(0);
                        v_isShared_6511_ = v_isSharedCheck_6529_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6490_ = leanh::lean_unsigned_to_nat(0);
                v___x_6491_ = lean_array_get_size(v_cs_6486_);
                v___x_6492_ = leanh::lean_box(0);
                v___x_6493_ = lean_nat_dec_lt(v___x_6490_, v___x_6491_);
                if v___x_6493_ == 0 {
                    leanh::lean_dec_ref(v_cs_6486_);
                    if v_isShared_6489_ == 0 {
                        leanh::lean_ctor_set(v___x_6488_, 0, v___x_6492_);
                        v___x_6495_ = v___x_6488_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6496_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6496_, 0, v___x_6492_);
                        v___x_6495_ = v_reuseFailAlloc_6496_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6497_ = lean_nat_dec_le(v___x_6491_, v___x_6491_);
                    if v___x_6497_ == 0 {
                        if v___x_6493_ == 0 {
                            leanh::lean_dec_ref(v_cs_6486_);
                            if v_isShared_6489_ == 0 {
                                leanh::lean_ctor_set(v___x_6488_, 0, v___x_6492_);
                                v___x_6499_ = v___x_6488_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_6500_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 0, v___x_6492_);
                                v___x_6499_ = v_reuseFailAlloc_6500_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_6488_);
                            v___x_6501_ = 0usize;
                            v___x_6502_ = lean_usize_of_nat(v___x_6491_);
                            v___x_6503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_6486_, v___x_6501_, v___x_6502_, v___x_6492_, v___y_6478_, v___y_6479_, v___y_6480_, v___y_6481_, v___y_6482_, v___y_6483_, v___y_6484_);
                            leanh::lean_dec_ref(v_cs_6486_);
                            return v___x_6503_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_6488_);
                        v___x_6504_ = 0usize;
                        v___x_6505_ = lean_usize_of_nat(v___x_6491_);
                        v___x_6506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_6486_, v___x_6504_, v___x_6505_, v___x_6492_, v___y_6478_, v___y_6479_, v___y_6480_, v___y_6481_, v___y_6482_, v___y_6483_, v___y_6484_);
                        leanh::lean_dec_ref(v_cs_6486_);
                        return v___x_6506_;
                    }
                }
            }
            2 => {
                return v___x_6495_;
            }
            3 => {
                return v___x_6499_;
            }
            4 => {
                v___x_6512_ = leanh::lean_unsigned_to_nat(0);
                v___x_6513_ = lean_array_get_size(v_vs_6508_);
                v___x_6514_ = leanh::lean_box(0);
                v___x_6515_ = lean_nat_dec_lt(v___x_6512_, v___x_6513_);
                if v___x_6515_ == 0 {
                    leanh::lean_dec_ref(v_vs_6508_);
                    if v_isShared_6511_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_6510_, 0);
                        leanh::lean_ctor_set(v___x_6510_, 0, v___x_6514_);
                        v___x_6517_ = v___x_6510_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6518_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6518_, 0, v___x_6514_);
                        v___x_6517_ = v_reuseFailAlloc_6518_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_6519_ = lean_nat_dec_le(v___x_6513_, v___x_6513_);
                    if v___x_6519_ == 0 {
                        if v___x_6515_ == 0 {
                            leanh::lean_dec_ref(v_vs_6508_);
                            if v_isShared_6511_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_6510_, 0);
                                leanh::lean_ctor_set(v___x_6510_, 0, v___x_6514_);
                                v___x_6521_ = v___x_6510_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_6522_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_6522_, 0, v___x_6514_);
                                v___x_6521_ = v_reuseFailAlloc_6522_;
                                state = 6;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_6510_);
                            v___x_6523_ = 0usize;
                            v___x_6524_ = lean_usize_of_nat(v___x_6513_);
                            v___x_6525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_6508_, v___x_6523_, v___x_6524_, v___x_6514_, v___y_6478_, v___y_6479_, v___y_6480_, v___y_6481_, v___y_6482_, v___y_6483_, v___y_6484_);
                            leanh::lean_dec_ref(v_vs_6508_);
                            return v___x_6525_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_6510_);
                        v___x_6526_ = 0usize;
                        v___x_6527_ = lean_usize_of_nat(v___x_6513_);
                        v___x_6528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_6508_, v___x_6526_, v___x_6527_, v___x_6514_, v___y_6478_, v___y_6479_, v___y_6480_, v___y_6481_, v___y_6482_, v___y_6483_, v___y_6484_);
                        leanh::lean_dec_ref(v_vs_6508_);
                        return v___x_6528_;
                    }
                }
            }
            5 => {
                return v___x_6517_;
            }
            6 => {
                return v___x_6521_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(
    mut v_as_6530_: *mut leanh::LeanObject,
    mut v_i_6531_: usize,
    mut v_stop_6532_: usize,
    mut v_b_6533_: *mut leanh::LeanObject,
    mut v___y_6534_: *mut leanh::LeanObject,
    mut v___y_6535_: *mut leanh::LeanObject,
    mut v___y_6536_: *mut leanh::LeanObject,
    mut v___y_6537_: *mut leanh::LeanObject,
    mut v___y_6538_: *mut leanh::LeanObject,
    mut v___y_6539_: *mut leanh::LeanObject,
    mut v___y_6540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6542_: u8 = 0;
    let mut v___x_6543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: usize = 0;
    let mut v___x_6547_: usize = 0;
    let mut v___x_6549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6542_ = lean_usize_dec_eq(v_i_6531_, v_stop_6532_);
                if v___x_6542_ == 0 {
                    v___x_6543_ = lean_array_uget_borrowed(v_as_6530_, v_i_6531_);
                    leanh::lean_inc(v___x_6543_);
                    v___x_6544_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v___x_6543_, v___y_6534_, v___y_6535_, v___y_6536_, v___y_6537_, v___y_6538_, v___y_6539_, v___y_6540_);
                    if leanh::lean_obj_tag(v___x_6544_) == 0 {
                        v_a_6545_ = leanh::lean_ctor_get(v___x_6544_, 0);
                        leanh::lean_inc(v_a_6545_);
                        leanh::lean_dec_ref_known(v___x_6544_, 1);
                        v___x_6546_ = 1usize;
                        v___x_6547_ = lean_usize_add(v_i_6531_, v___x_6546_);
                        v_i_6531_ = v___x_6547_;
                        v_b_6533_ = v_a_6545_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6544_;
                    }
                } else {
                    v___x_6549_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6549_, 0, v_b_6533_);
                    return v___x_6549_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4___boxed(
    mut v_as_6550_: *mut leanh::LeanObject,
    mut v_i_6551_: *mut leanh::LeanObject,
    mut v_stop_6552_: *mut leanh::LeanObject,
    mut v_b_6553_: *mut leanh::LeanObject,
    mut v___y_6554_: *mut leanh::LeanObject,
    mut v___y_6555_: *mut leanh::LeanObject,
    mut v___y_6556_: *mut leanh::LeanObject,
    mut v___y_6557_: *mut leanh::LeanObject,
    mut v___y_6558_: *mut leanh::LeanObject,
    mut v___y_6559_: *mut leanh::LeanObject,
    mut v___y_6560_: *mut leanh::LeanObject,
    mut v___y_6561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6562_: usize = 0;
    let mut v_stop_boxed_6563_: usize = 0;
    let mut v_res_6564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6562_ = leanh::lean_unbox_usize(v_i_6551_);
    leanh::lean_dec(v_i_6551_);
    v_stop_boxed_6563_ = leanh::lean_unbox_usize(v_stop_6552_);
    leanh::lean_dec(v_stop_6552_);
    v_res_6564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_as_6550_, v_i_boxed_6562_, v_stop_boxed_6563_, v_b_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_);
    leanh::lean_dec(v___y_6560_);
    leanh::lean_dec_ref(v___y_6559_);
    leanh::lean_dec(v___y_6558_);
    leanh::lean_dec_ref(v___y_6557_);
    leanh::lean_dec(v___y_6556_);
    leanh::lean_dec(v___y_6555_);
    leanh::lean_dec_ref(v___y_6554_);
    leanh::lean_dec_ref(v_as_6550_);
    return v_res_6564_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3___boxed(
    mut v_x_6565_: *mut leanh::LeanObject,
    mut v___y_6566_: *mut leanh::LeanObject,
    mut v___y_6567_: *mut leanh::LeanObject,
    mut v___y_6568_: *mut leanh::LeanObject,
    mut v___y_6569_: *mut leanh::LeanObject,
    mut v___y_6570_: *mut leanh::LeanObject,
    mut v___y_6571_: *mut leanh::LeanObject,
    mut v___y_6572_: *mut leanh::LeanObject,
    mut v___y_6573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6574_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_x_6565_, v___y_6566_, v___y_6567_, v___y_6568_, v___y_6569_, v___y_6570_, v___y_6571_, v___y_6572_);
    leanh::lean_dec(v___y_6572_);
    leanh::lean_dec_ref(v___y_6571_);
    leanh::lean_dec(v___y_6570_);
    leanh::lean_dec_ref(v___y_6569_);
    leanh::lean_dec(v___y_6568_);
    leanh::lean_dec(v___y_6567_);
    leanh::lean_dec_ref(v___y_6566_);
    return v_res_6574_;
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(
    mut v_t_6575_: *mut leanh::LeanObject,
    mut v___y_6576_: *mut leanh::LeanObject,
    mut v___y_6577_: *mut leanh::LeanObject,
    mut v___y_6578_: *mut leanh::LeanObject,
    mut v___y_6579_: *mut leanh::LeanObject,
    mut v___y_6580_: *mut leanh::LeanObject,
    mut v___y_6581_: *mut leanh::LeanObject,
    mut v___y_6582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_6584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6589_: u8 = 0;
    let mut v___x_6590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: u8 = 0;
    let mut v___x_6595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: u8 = 0;
    let mut v___x_6599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6601_: usize = 0;
    let mut v___x_6602_: usize = 0;
    let mut v___x_6603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: usize = 0;
    let mut v___x_6605_: usize = 0;
    let mut v___x_6606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6607_: u8 = 0;
    let mut v_unused_6608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_6584_ = leanh::lean_ctor_get(v_t_6575_, 0);
                leanh::lean_inc_ref(v_root_6584_);
                v_tail_6585_ = leanh::lean_ctor_get(v_t_6575_, 1);
                leanh::lean_inc_ref(v_tail_6585_);
                leanh::lean_dec_ref(v_t_6575_);
                v___x_6586_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__3(v_root_6584_, v___y_6576_, v___y_6577_, v___y_6578_, v___y_6579_, v___y_6580_, v___y_6581_, v___y_6582_);
                if leanh::lean_obj_tag(v___x_6586_) == 0 {
                    v_isSharedCheck_6607_ = (!leanh::lean_is_exclusive(v___x_6586_)) as u8;
                    if v_isSharedCheck_6607_ == 0 {
                        v_unused_6608_ = leanh::lean_ctor_get(v___x_6586_, 0);
                        leanh::lean_dec(v_unused_6608_);
                        v___x_6588_ = v___x_6586_;
                        v_isShared_6589_ = v_isSharedCheck_6607_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6586_);
                        v___x_6588_ = leanh::lean_box(0);
                        v_isShared_6589_ = v_isSharedCheck_6607_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_tail_6585_);
                    return v___x_6586_;
                }
            }
            1 => {
                v___x_6590_ = leanh::lean_unsigned_to_nat(0);
                v___x_6591_ = lean_array_get_size(v_tail_6585_);
                v___x_6592_ = leanh::lean_box(0);
                v___x_6593_ = lean_nat_dec_lt(v___x_6590_, v___x_6591_);
                if v___x_6593_ == 0 {
                    leanh::lean_dec_ref(v_tail_6585_);
                    if v_isShared_6589_ == 0 {
                        leanh::lean_ctor_set(v___x_6588_, 0, v___x_6592_);
                        v___x_6595_ = v___x_6588_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6596_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6596_, 0, v___x_6592_);
                        v___x_6595_ = v_reuseFailAlloc_6596_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6597_ = lean_nat_dec_le(v___x_6591_, v___x_6591_);
                    if v___x_6597_ == 0 {
                        if v___x_6593_ == 0 {
                            leanh::lean_dec_ref(v_tail_6585_);
                            if v_isShared_6589_ == 0 {
                                leanh::lean_ctor_set(v___x_6588_, 0, v___x_6592_);
                                v___x_6599_ = v___x_6588_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_6600_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_6600_, 0, v___x_6592_);
                                v___x_6599_ = v_reuseFailAlloc_6600_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_6588_);
                            v___x_6601_ = 0usize;
                            v___x_6602_ = lean_usize_of_nat(v___x_6591_);
                            v___x_6603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_6585_, v___x_6601_, v___x_6602_, v___x_6592_, v___y_6576_, v___y_6577_, v___y_6578_, v___y_6579_, v___y_6580_, v___y_6581_, v___y_6582_);
                            leanh::lean_dec_ref(v_tail_6585_);
                            return v___x_6603_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_6588_);
                        v___x_6604_ = 0usize;
                        v___x_6605_ = lean_usize_of_nat(v___x_6591_);
                        v___x_6606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_6585_, v___x_6604_, v___x_6605_, v___x_6592_, v___y_6576_, v___y_6577_, v___y_6578_, v___y_6579_, v___y_6580_, v___y_6581_, v___y_6582_);
                        leanh::lean_dec_ref(v_tail_6585_);
                        return v___x_6606_;
                    }
                }
            }
            2 => {
                return v___x_6595_;
            }
            3 => {
                return v___x_6599_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4___boxed(
    mut v_t_6609_: *mut leanh::LeanObject,
    mut v___y_6610_: *mut leanh::LeanObject,
    mut v___y_6611_: *mut leanh::LeanObject,
    mut v___y_6612_: *mut leanh::LeanObject,
    mut v___y_6613_: *mut leanh::LeanObject,
    mut v___y_6614_: *mut leanh::LeanObject,
    mut v___y_6615_: *mut leanh::LeanObject,
    mut v___y_6616_: *mut leanh::LeanObject,
    mut v___y_6617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6618_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_6609_, v___y_6610_, v___y_6611_, v___y_6612_, v___y_6613_, v___y_6614_, v___y_6615_, v___y_6616_);
    leanh::lean_dec(v___y_6616_);
    leanh::lean_dec_ref(v___y_6615_);
    leanh::lean_dec(v___y_6614_);
    leanh::lean_dec_ref(v___y_6613_);
    leanh::lean_dec(v___y_6612_);
    leanh::lean_dec(v___y_6611_);
    leanh::lean_dec_ref(v___y_6610_);
    return v_res_6618_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6619_ = l_Lean_instInhabitedPersistentArrayNode_default(leanh::lean_box(0));
    return v___x_6619_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(
    mut v_x_6620_: *mut leanh::LeanObject,
    mut v_x_6621_: usize,
    mut v_x_6622_: usize,
    mut v___y_6623_: *mut leanh::LeanObject,
    mut v___y_6624_: *mut leanh::LeanObject,
    mut v___y_6625_: *mut leanh::LeanObject,
    mut v___y_6626_: *mut leanh::LeanObject,
    mut v___y_6627_: *mut leanh::LeanObject,
    mut v___y_6628_: *mut leanh::LeanObject,
    mut v___y_6629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_6631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: usize = 0;
    let mut v_j_6634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: usize = 0;
    let mut v___x_6637_: usize = 0;
    let mut v___x_6638_: usize = 0;
    let mut v___x_6639_: usize = 0;
    let mut v___x_6640_: usize = 0;
    let mut v___x_6641_: usize = 0;
    let mut v___x_6642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6645_: u8 = 0;
    let mut v___x_6646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: u8 = 0;
    let mut v___x_6652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: u8 = 0;
    let mut v___x_6656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: usize = 0;
    let mut v___x_6659_: usize = 0;
    let mut v___x_6660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6661_: usize = 0;
    let mut v___x_6662_: usize = 0;
    let mut v___x_6663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6664_: u8 = 0;
    let mut v_unused_6665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_6666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6669_: u8 = 0;
    let mut v___x_6670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: u8 = 0;
    let mut v___x_6675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: u8 = 0;
    let mut v___x_6679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: usize = 0;
    let mut v___x_6682_: usize = 0;
    let mut v___x_6683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6684_: usize = 0;
    let mut v___x_6685_: usize = 0;
    let mut v___x_6686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6687_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6620_) == 0 {
                    v_cs_6631_ = leanh::lean_ctor_get(v_x_6620_, 0);
                    leanh::lean_inc_ref(v_cs_6631_);
                    leanh::lean_dec_ref_known(v_x_6620_, 1);
                    v___x_6632_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___closed__0);
                    v___x_6633_ = lean_usize_shift_right(v_x_6621_, v_x_6622_);
                    v_j_6634_ = lean_usize_to_nat(v___x_6633_);
                    v___x_6635_ = lean_array_get_borrowed(v___x_6632_, v_cs_6631_, v_j_6634_);
                    v___x_6636_ = 1usize;
                    v___x_6637_ = lean_usize_shift_left(v___x_6636_, v_x_6622_);
                    v___x_6638_ = lean_usize_sub(v___x_6637_, v___x_6636_);
                    v___x_6639_ = lean_usize_land(v_x_6621_, v___x_6638_);
                    v___x_6640_ = 5usize;
                    v___x_6641_ = lean_usize_sub(v_x_6622_, v___x_6640_);
                    leanh::lean_inc(v___x_6635_);
                    v___x_6642_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v___x_6635_, v___x_6639_, v___x_6641_, v___y_6623_, v___y_6624_, v___y_6625_, v___y_6626_, v___y_6627_, v___y_6628_, v___y_6629_);
                    if leanh::lean_obj_tag(v___x_6642_) == 0 {
                        v_isSharedCheck_6664_ =
                            (!leanh::lean_is_exclusive(v___x_6642_)) as u8;
                        if v_isSharedCheck_6664_ == 0 {
                            v_unused_6665_ = leanh::lean_ctor_get(v___x_6642_, 0);
                            leanh::lean_dec(v_unused_6665_);
                            v___x_6644_ = v___x_6642_;
                            v_isShared_6645_ = v_isSharedCheck_6664_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_6642_);
                            v___x_6644_ = leanh::lean_box(0);
                            v_isShared_6645_ = v_isSharedCheck_6664_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_j_6634_);
                        leanh::lean_dec_ref(v_cs_6631_);
                        return v___x_6642_;
                    }
                } else {
                    v_vs_6666_ = leanh::lean_ctor_get(v_x_6620_, 0);
                    v_isSharedCheck_6687_ = (!leanh::lean_is_exclusive(v_x_6620_)) as u8;
                    if v_isSharedCheck_6687_ == 0 {
                        v___x_6668_ = v_x_6620_;
                        v_isShared_6669_ = v_isSharedCheck_6687_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_6666_);
                        leanh::lean_dec(v_x_6620_);
                        v___x_6668_ = leanh::lean_box(0);
                        v_isShared_6669_ = v_isSharedCheck_6687_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6646_ = leanh::lean_unsigned_to_nat(1);
                v___x_6647_ = lean_nat_add(v_j_6634_, v___x_6646_);
                leanh::lean_dec(v_j_6634_);
                v___x_6648_ = lean_array_get_size(v_cs_6631_);
                v___x_6649_ = leanh::lean_box(0);
                v___x_6650_ = lean_nat_dec_lt(v___x_6647_, v___x_6648_);
                if v___x_6650_ == 0 {
                    leanh::lean_dec(v___x_6647_);
                    leanh::lean_dec_ref(v_cs_6631_);
                    if v_isShared_6645_ == 0 {
                        leanh::lean_ctor_set(v___x_6644_, 0, v___x_6649_);
                        v___x_6652_ = v___x_6644_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6653_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6653_, 0, v___x_6649_);
                        v___x_6652_ = v_reuseFailAlloc_6653_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6654_ = lean_nat_dec_le(v___x_6648_, v___x_6648_);
                    if v___x_6654_ == 0 {
                        if v___x_6650_ == 0 {
                            leanh::lean_dec(v___x_6647_);
                            leanh::lean_dec_ref(v_cs_6631_);
                            if v_isShared_6645_ == 0 {
                                leanh::lean_ctor_set(v___x_6644_, 0, v___x_6649_);
                                v___x_6656_ = v___x_6644_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_6657_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_6657_, 0, v___x_6649_);
                                v___x_6656_ = v_reuseFailAlloc_6657_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_6644_);
                            v___x_6658_ = lean_usize_of_nat(v___x_6647_);
                            leanh::lean_dec(v___x_6647_);
                            v___x_6659_ = lean_usize_of_nat(v___x_6648_);
                            v___x_6660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_6631_, v___x_6658_, v___x_6659_, v___x_6649_, v___y_6623_, v___y_6624_, v___y_6625_, v___y_6626_, v___y_6627_, v___y_6628_, v___y_6629_);
                            leanh::lean_dec_ref(v_cs_6631_);
                            return v___x_6660_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_6644_);
                        v___x_6661_ = lean_usize_of_nat(v___x_6647_);
                        leanh::lean_dec(v___x_6647_);
                        v___x_6662_ = lean_usize_of_nat(v___x_6648_);
                        v___x_6663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2_spec__4(v_cs_6631_, v___x_6661_, v___x_6662_, v___x_6649_, v___y_6623_, v___y_6624_, v___y_6625_, v___y_6626_, v___y_6627_, v___y_6628_, v___y_6629_);
                        leanh::lean_dec_ref(v_cs_6631_);
                        return v___x_6663_;
                    }
                }
            }
            2 => {
                return v___x_6652_;
            }
            3 => {
                return v___x_6656_;
            }
            4 => {
                v___x_6670_ = lean_usize_to_nat(v_x_6621_);
                v___x_6671_ = lean_array_get_size(v_vs_6666_);
                v___x_6672_ = leanh::lean_box(0);
                v___x_6673_ = lean_nat_dec_lt(v___x_6670_, v___x_6671_);
                if v___x_6673_ == 0 {
                    leanh::lean_dec(v___x_6670_);
                    leanh::lean_dec_ref(v_vs_6666_);
                    if v_isShared_6669_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_6668_, 0);
                        leanh::lean_ctor_set(v___x_6668_, 0, v___x_6672_);
                        v___x_6675_ = v___x_6668_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6676_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6676_, 0, v___x_6672_);
                        v___x_6675_ = v_reuseFailAlloc_6676_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_6677_ = lean_nat_dec_le(v___x_6671_, v___x_6671_);
                    if v___x_6677_ == 0 {
                        if v___x_6673_ == 0 {
                            leanh::lean_dec(v___x_6670_);
                            leanh::lean_dec_ref(v_vs_6666_);
                            if v_isShared_6669_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_6668_, 0);
                                leanh::lean_ctor_set(v___x_6668_, 0, v___x_6672_);
                                v___x_6679_ = v___x_6668_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_6680_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_6680_, 0, v___x_6672_);
                                v___x_6679_ = v_reuseFailAlloc_6680_;
                                state = 6;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_6668_);
                            v___x_6681_ = lean_usize_of_nat(v___x_6670_);
                            leanh::lean_dec(v___x_6670_);
                            v___x_6682_ = lean_usize_of_nat(v___x_6671_);
                            v___x_6683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_6666_, v___x_6681_, v___x_6682_, v___x_6672_, v___y_6623_, v___y_6624_, v___y_6625_, v___y_6626_, v___y_6627_, v___y_6628_, v___y_6629_);
                            leanh::lean_dec_ref(v_vs_6666_);
                            return v___x_6683_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_6668_);
                        v___x_6684_ = lean_usize_of_nat(v___x_6670_);
                        leanh::lean_dec(v___x_6670_);
                        v___x_6685_ = lean_usize_of_nat(v___x_6671_);
                        v___x_6686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_vs_6666_, v___x_6684_, v___x_6685_, v___x_6672_, v___y_6623_, v___y_6624_, v___y_6625_, v___y_6626_, v___y_6627_, v___y_6628_, v___y_6629_);
                        leanh::lean_dec_ref(v_vs_6666_);
                        return v___x_6686_;
                    }
                }
            }
            5 => {
                return v___x_6675_;
            }
            6 => {
                return v___x_6679_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2___boxed(
    mut v_x_6688_: *mut leanh::LeanObject,
    mut v_x_6689_: *mut leanh::LeanObject,
    mut v_x_6690_: *mut leanh::LeanObject,
    mut v___y_6691_: *mut leanh::LeanObject,
    mut v___y_6692_: *mut leanh::LeanObject,
    mut v___y_6693_: *mut leanh::LeanObject,
    mut v___y_6694_: *mut leanh::LeanObject,
    mut v___y_6695_: *mut leanh::LeanObject,
    mut v___y_6696_: *mut leanh::LeanObject,
    mut v___y_6697_: *mut leanh::LeanObject,
    mut v___y_6698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_10795__boxed_6699_: usize = 0;
    let mut v_x_10796__boxed_6700_: usize = 0;
    let mut v_res_6701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_10795__boxed_6699_ = leanh::lean_unbox_usize(v_x_6689_);
    leanh::lean_dec(v_x_6689_);
    v_x_10796__boxed_6700_ = leanh::lean_unbox_usize(v_x_6690_);
    leanh::lean_dec(v_x_6690_);
    v_res_6701_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_x_6688_, v_x_10795__boxed_6699_, v_x_10796__boxed_6700_, v___y_6691_, v___y_6692_, v___y_6693_, v___y_6694_, v___y_6695_, v___y_6696_, v___y_6697_);
    leanh::lean_dec(v___y_6697_);
    leanh::lean_dec_ref(v___y_6696_);
    leanh::lean_dec(v___y_6695_);
    leanh::lean_dec_ref(v___y_6694_);
    leanh::lean_dec(v___y_6693_);
    leanh::lean_dec(v___y_6692_);
    leanh::lean_dec_ref(v___y_6691_);
    return v_res_6701_;
}
pub unsafe fn l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(
    mut v_t_6702_: *mut leanh::LeanObject,
    mut v_start_6703_: *mut leanh::LeanObject,
    mut v___y_6704_: *mut leanh::LeanObject,
    mut v___y_6705_: *mut leanh::LeanObject,
    mut v___y_6706_: *mut leanh::LeanObject,
    mut v___y_6707_: *mut leanh::LeanObject,
    mut v___y_6708_: *mut leanh::LeanObject,
    mut v___y_6709_: *mut leanh::LeanObject,
    mut v___y_6710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6713_: u8 = 0;
    let mut v_root_6714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_6716_: usize = 0;
    let mut v_tailOff_6717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6718_: u8 = 0;
    let mut v___x_6719_: usize = 0;
    let mut v___x_6720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6723_: u8 = 0;
    let mut v___x_6724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: u8 = 0;
    let mut v___x_6728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6730_: u8 = 0;
    let mut v___x_6732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6734_: usize = 0;
    let mut v___x_6735_: usize = 0;
    let mut v___x_6736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: usize = 0;
    let mut v___x_6738_: usize = 0;
    let mut v___x_6739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6740_: u8 = 0;
    let mut v_unused_6741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: u8 = 0;
    let mut v___x_6746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: u8 = 0;
    let mut v___x_6748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: usize = 0;
    let mut v___x_6750_: usize = 0;
    let mut v___x_6751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: usize = 0;
    let mut v___x_6753_: usize = 0;
    let mut v___x_6754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6712_ = leanh::lean_unsigned_to_nat(0);
                v___x_6713_ = lean_nat_dec_eq(v_start_6703_, v___x_6712_);
                if v___x_6713_ == 0 {
                    v_root_6714_ = leanh::lean_ctor_get(v_t_6702_, 0);
                    leanh::lean_inc_ref(v_root_6714_);
                    v_tail_6715_ = leanh::lean_ctor_get(v_t_6702_, 1);
                    leanh::lean_inc_ref(v_tail_6715_);
                    v_shift_6716_ = leanh::lean_ctor_get_usize(v_t_6702_, 4);
                    v_tailOff_6717_ = leanh::lean_ctor_get(v_t_6702_, 3);
                    leanh::lean_inc(v_tailOff_6717_);
                    leanh::lean_dec_ref(v_t_6702_);
                    v___x_6718_ = lean_nat_dec_le(v_tailOff_6717_, v_start_6703_);
                    if v___x_6718_ == 0 {
                        leanh::lean_dec(v_tailOff_6717_);
                        v___x_6719_ = lean_usize_of_nat(v_start_6703_);
                        v___x_6720_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__2(v_root_6714_, v___x_6719_, v_shift_6716_, v___y_6704_, v___y_6705_, v___y_6706_, v___y_6707_, v___y_6708_, v___y_6709_, v___y_6710_);
                        if leanh::lean_obj_tag(v___x_6720_) == 0 {
                            v_isSharedCheck_6740_ =
                                (!leanh::lean_is_exclusive(v___x_6720_)) as u8;
                            if v_isSharedCheck_6740_ == 0 {
                                v_unused_6741_ = leanh::lean_ctor_get(v___x_6720_, 0);
                                leanh::lean_dec(v_unused_6741_);
                                v___x_6722_ = v___x_6720_;
                                v_isShared_6723_ = v_isSharedCheck_6740_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_6720_);
                                v___x_6722_ = leanh::lean_box(0);
                                v_isShared_6723_ = v_isSharedCheck_6740_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_tail_6715_);
                            return v___x_6720_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_root_6714_);
                        v___x_6742_ = lean_nat_sub(v_start_6703_, v_tailOff_6717_);
                        leanh::lean_dec(v_tailOff_6717_);
                        v___x_6743_ = lean_array_get_size(v_tail_6715_);
                        v___x_6744_ = leanh::lean_box(0);
                        v___x_6745_ = lean_nat_dec_lt(v___x_6742_, v___x_6743_);
                        if v___x_6745_ == 0 {
                            leanh::lean_dec(v___x_6742_);
                            leanh::lean_dec_ref(v_tail_6715_);
                            v___x_6746_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_6746_, 0, v___x_6744_);
                            return v___x_6746_;
                        } else {
                            v___x_6747_ = lean_nat_dec_le(v___x_6743_, v___x_6743_);
                            if v___x_6747_ == 0 {
                                if v___x_6745_ == 0 {
                                    leanh::lean_dec(v___x_6742_);
                                    leanh::lean_dec_ref(v_tail_6715_);
                                    v___x_6748_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_6748_, 0, v___x_6744_);
                                    return v___x_6748_;
                                } else {
                                    v___x_6749_ = lean_usize_of_nat(v___x_6742_);
                                    leanh::lean_dec(v___x_6742_);
                                    v___x_6750_ = lean_usize_of_nat(v___x_6743_);
                                    v___x_6751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_6715_, v___x_6749_, v___x_6750_, v___x_6744_, v___y_6704_, v___y_6705_, v___y_6706_, v___y_6707_, v___y_6708_, v___y_6709_, v___y_6710_);
                                    leanh::lean_dec_ref(v_tail_6715_);
                                    return v___x_6751_;
                                }
                            } else {
                                v___x_6752_ = lean_usize_of_nat(v___x_6742_);
                                leanh::lean_dec(v___x_6742_);
                                v___x_6753_ = lean_usize_of_nat(v___x_6743_);
                                v___x_6754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_6715_, v___x_6752_, v___x_6753_, v___x_6744_, v___y_6704_, v___y_6705_, v___y_6706_, v___y_6707_, v___y_6708_, v___y_6709_, v___y_6710_);
                                leanh::lean_dec_ref(v_tail_6715_);
                                return v___x_6754_;
                            }
                        }
                    }
                } else {
                    v___x_6755_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__4(v_t_6702_, v___y_6704_, v___y_6705_, v___y_6706_, v___y_6707_, v___y_6708_, v___y_6709_, v___y_6710_);
                    return v___x_6755_;
                }
            }
            1 => {
                v___x_6724_ = lean_array_get_size(v_tail_6715_);
                v___x_6725_ = leanh::lean_box(0);
                v___x_6726_ = lean_nat_dec_lt(v___x_6712_, v___x_6724_);
                if v___x_6726_ == 0 {
                    leanh::lean_dec_ref(v_tail_6715_);
                    if v_isShared_6723_ == 0 {
                        leanh::lean_ctor_set(v___x_6722_, 0, v___x_6725_);
                        v___x_6728_ = v___x_6722_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6729_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6729_, 0, v___x_6725_);
                        v___x_6728_ = v_reuseFailAlloc_6729_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6730_ = lean_nat_dec_le(v___x_6724_, v___x_6724_);
                    if v___x_6730_ == 0 {
                        if v___x_6726_ == 0 {
                            leanh::lean_dec_ref(v_tail_6715_);
                            if v_isShared_6723_ == 0 {
                                leanh::lean_ctor_set(v___x_6722_, 0, v___x_6725_);
                                v___x_6732_ = v___x_6722_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_6733_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_6733_, 0, v___x_6725_);
                                v___x_6732_ = v_reuseFailAlloc_6733_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_6722_);
                            v___x_6734_ = 0usize;
                            v___x_6735_ = lean_usize_of_nat(v___x_6724_);
                            v___x_6736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_6715_, v___x_6734_, v___x_6735_, v___x_6725_, v___y_6704_, v___y_6705_, v___y_6706_, v___y_6707_, v___y_6708_, v___y_6709_, v___y_6710_);
                            leanh::lean_dec_ref(v_tail_6715_);
                            return v___x_6736_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_6722_);
                        v___x_6737_ = 0usize;
                        v___x_6738_ = lean_usize_of_nat(v___x_6724_);
                        v___x_6739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1_spec__3(v_tail_6715_, v___x_6737_, v___x_6738_, v___x_6725_, v___y_6704_, v___y_6705_, v___y_6706_, v___y_6707_, v___y_6708_, v___y_6709_, v___y_6710_);
                        leanh::lean_dec_ref(v_tail_6715_);
                        return v___x_6739_;
                    }
                }
            }
            2 => {
                return v___x_6728_;
            }
            3 => {
                return v___x_6732_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1___boxed(
    mut v_t_6756_: *mut leanh::LeanObject,
    mut v_start_6757_: *mut leanh::LeanObject,
    mut v___y_6758_: *mut leanh::LeanObject,
    mut v___y_6759_: *mut leanh::LeanObject,
    mut v___y_6760_: *mut leanh::LeanObject,
    mut v___y_6761_: *mut leanh::LeanObject,
    mut v___y_6762_: *mut leanh::LeanObject,
    mut v___y_6763_: *mut leanh::LeanObject,
    mut v___y_6764_: *mut leanh::LeanObject,
    mut v___y_6765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6766_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_t_6756_, v_start_6757_, v___y_6758_, v___y_6759_, v___y_6760_, v___y_6761_, v___y_6762_, v___y_6763_, v___y_6764_);
    leanh::lean_dec(v___y_6764_);
    leanh::lean_dec_ref(v___y_6763_);
    leanh::lean_dec(v___y_6762_);
    leanh::lean_dec_ref(v___y_6761_);
    leanh::lean_dec(v___y_6760_);
    leanh::lean_dec(v___y_6759_);
    leanh::lean_dec_ref(v___y_6758_);
    leanh::lean_dec(v_start_6757_);
    return v_res_6766_;
}
pub unsafe fn l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(
    mut v_lctx_6767_: *mut leanh::LeanObject,
    mut v_start_6768_: *mut leanh::LeanObject,
    mut v___y_6769_: *mut leanh::LeanObject,
    mut v___y_6770_: *mut leanh::LeanObject,
    mut v___y_6771_: *mut leanh::LeanObject,
    mut v___y_6772_: *mut leanh::LeanObject,
    mut v___y_6773_: *mut leanh::LeanObject,
    mut v___y_6774_: *mut leanh::LeanObject,
    mut v___y_6775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decls_6777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_decls_6777_ = leanh::lean_ctor_get(v_lctx_6767_, 1);
    leanh::lean_inc_ref(v_decls_6777_);
    leanh::lean_dec_ref(v_lctx_6767_);
    v___x_6778_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1_spec__1(v_decls_6777_, v_start_6768_, v___y_6769_, v___y_6770_, v___y_6771_, v___y_6772_, v___y_6773_, v___y_6774_, v___y_6775_);
    return v___x_6778_;
}
pub unsafe fn l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1___boxed(
    mut v_lctx_6779_: *mut leanh::LeanObject,
    mut v_start_6780_: *mut leanh::LeanObject,
    mut v___y_6781_: *mut leanh::LeanObject,
    mut v___y_6782_: *mut leanh::LeanObject,
    mut v___y_6783_: *mut leanh::LeanObject,
    mut v___y_6784_: *mut leanh::LeanObject,
    mut v___y_6785_: *mut leanh::LeanObject,
    mut v___y_6786_: *mut leanh::LeanObject,
    mut v___y_6787_: *mut leanh::LeanObject,
    mut v___y_6788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6789_ =
        l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(
            v_lctx_6779_,
            v_start_6780_,
            v___y_6781_,
            v___y_6782_,
            v___y_6783_,
            v___y_6784_,
            v___y_6785_,
            v___y_6786_,
            v___y_6787_,
        );
    leanh::lean_dec(v___y_6787_);
    leanh::lean_dec_ref(v___y_6786_);
    leanh::lean_dec(v___y_6785_);
    leanh::lean_dec_ref(v___y_6784_);
    leanh::lean_dec(v___y_6783_);
    leanh::lean_dec(v___y_6782_);
    leanh::lean_dec_ref(v___y_6781_);
    leanh::lean_dec(v_start_6780_);
    return v_res_6789_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_initializeValueMap(
    mut v_a_6790_: *mut leanh::LeanObject,
    mut v_a_6791_: *mut leanh::LeanObject,
    mut v_a_6792_: *mut leanh::LeanObject,
    mut v_a_6793_: *mut leanh::LeanObject,
    mut v_a_6794_: *mut leanh::LeanObject,
    mut v_a_6795_: *mut leanh::LeanObject,
    mut v_a_6796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_6798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lctx_6798_ = leanh::lean_ctor_get(v_a_6793_, 2);
    v___x_6799_ = leanh::lean_unsigned_to_nat(0);
    leanh::lean_inc_ref(v_lctx_6798_);
    v___x_6800_ =
        l_Lean_LocalContext_forM___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__1(
            v_lctx_6798_,
            v___x_6799_,
            v_a_6790_,
            v_a_6791_,
            v_a_6792_,
            v_a_6793_,
            v_a_6794_,
            v_a_6795_,
            v_a_6796_,
        );
    return v___x_6800_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_initializeValueMap___boxed(
    mut v_a_6801_: *mut leanh::LeanObject,
    mut v_a_6802_: *mut leanh::LeanObject,
    mut v_a_6803_: *mut leanh::LeanObject,
    mut v_a_6804_: *mut leanh::LeanObject,
    mut v_a_6805_: *mut leanh::LeanObject,
    mut v_a_6806_: *mut leanh::LeanObject,
    mut v_a_6807_: *mut leanh::LeanObject,
    mut v_a_6808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6809_ = l_Lean_Meta_ExtractLets_initializeValueMap(
        v_a_6801_, v_a_6802_, v_a_6803_, v_a_6804_, v_a_6805_, v_a_6806_, v_a_6807_,
    );
    leanh::lean_dec(v_a_6807_);
    leanh::lean_dec_ref(v_a_6806_);
    leanh::lean_dec(v_a_6805_);
    leanh::lean_dec_ref(v_a_6804_);
    leanh::lean_dec(v_a_6803_);
    leanh::lean_dec(v_a_6802_);
    leanh::lean_dec_ref(v_a_6801_);
    return v_res_6809_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_containsLet(
    mut v_e_6811_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_6812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6812_ = l_Lean_Meta_ExtractLets_containsLet___closed__0;
    v___x_6813_ = lean_find_expr(v___f_6812_, v_e_6811_);
    if leanh::lean_obj_tag(v___x_6813_) == 0 {
        let mut v___x_6814_: u8 = 0;
        v___x_6814_ = 0;
        return v___x_6814_;
    } else {
        let mut v___x_6815_: u8 = 0;
        leanh::lean_dec_ref_known(v___x_6813_, 1);
        v___x_6815_ = 1;
        return v___x_6815_;
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_containsLet___boxed(
    mut v_e_6816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6817_: u8 = 0;
    let mut v_r_6818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6817_ = l_Lean_Meta_ExtractLets_containsLet(v_e_6816_);
    leanh::lean_dec_ref(v_e_6816_);
    v_r_6818_ = leanh::lean_box((v_res_6817_) as usize);
    return v_r_6818_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(
    mut v_k_6819_: *mut leanh::LeanObject,
    mut v___y_6820_: *mut leanh::LeanObject,
    mut v___y_6821_: *mut leanh::LeanObject,
    mut v___y_6822_: *mut leanh::LeanObject,
    mut v_b_6823_: *mut leanh::LeanObject,
    mut v___y_6824_: *mut leanh::LeanObject,
    mut v___y_6825_: *mut leanh::LeanObject,
    mut v___y_6826_: *mut leanh::LeanObject,
    mut v___y_6827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6829_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_6827_);
    leanh::lean_inc_ref(v___y_6826_);
    leanh::lean_inc(v___y_6825_);
    leanh::lean_inc_ref(v___y_6824_);
    leanh::lean_inc(v___y_6822_);
    leanh::lean_inc(v___y_6821_);
    leanh::lean_inc_ref(v___y_6820_);
    v___x_6829_ = leanh::lean_apply_9(
        v_k_6819_,
        v_b_6823_,
        v___y_6820_,
        v___y_6821_,
        v___y_6822_,
        v___y_6824_,
        v___y_6825_,
        v___y_6826_,
        v___y_6827_,
        leanh::lean_box(0),
    );
    return v___x_6829_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed(
    mut v_k_6830_: *mut leanh::LeanObject,
    mut v___y_6831_: *mut leanh::LeanObject,
    mut v___y_6832_: *mut leanh::LeanObject,
    mut v___y_6833_: *mut leanh::LeanObject,
    mut v_b_6834_: *mut leanh::LeanObject,
    mut v___y_6835_: *mut leanh::LeanObject,
    mut v___y_6836_: *mut leanh::LeanObject,
    mut v___y_6837_: *mut leanh::LeanObject,
    mut v___y_6838_: *mut leanh::LeanObject,
    mut v___y_6839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6840_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0(v_k_6830_, v___y_6831_, v___y_6832_, v___y_6833_, v_b_6834_, v___y_6835_, v___y_6836_, v___y_6837_, v___y_6838_);
    leanh::lean_dec(v___y_6838_);
    leanh::lean_dec_ref(v___y_6837_);
    leanh::lean_dec(v___y_6836_);
    leanh::lean_dec_ref(v___y_6835_);
    leanh::lean_dec(v___y_6833_);
    leanh::lean_dec(v___y_6832_);
    leanh::lean_dec_ref(v___y_6831_);
    return v_res_6840_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(
    mut v_name_6841_: *mut leanh::LeanObject,
    mut v_bi_6842_: u8,
    mut v_type_6843_: *mut leanh::LeanObject,
    mut v_k_6844_: *mut leanh::LeanObject,
    mut v_kind_6845_: u8,
    mut v___y_6846_: *mut leanh::LeanObject,
    mut v___y_6847_: *mut leanh::LeanObject,
    mut v___y_6848_: *mut leanh::LeanObject,
    mut v___y_6849_: *mut leanh::LeanObject,
    mut v___y_6850_: *mut leanh::LeanObject,
    mut v___y_6851_: *mut leanh::LeanObject,
    mut v___y_6852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6859_: u8 = 0;
    let mut v___x_6861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6863_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_6848_);
                leanh::lean_inc(v___y_6847_);
                leanh::lean_inc_ref(v___y_6846_);
                v___f_6854_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                leanh::lean_closure_set(v___f_6854_, 0, v_k_6844_);
                leanh::lean_closure_set(v___f_6854_, 1, v___y_6846_);
                leanh::lean_closure_set(v___f_6854_, 2, v___y_6847_);
                leanh::lean_closure_set(v___f_6854_, 3, v___y_6848_);
                v___x_6855_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
                    v_name_6841_,
                    v_bi_6842_,
                    v_type_6843_,
                    v___f_6854_,
                    v_kind_6845_,
                    v___y_6849_,
                    v___y_6850_,
                    v___y_6851_,
                    v___y_6852_,
                );
                if leanh::lean_obj_tag(v___x_6855_) == 0 {
                    return v___x_6855_;
                } else {
                    v_a_6856_ = leanh::lean_ctor_get(v___x_6855_, 0);
                    v_isSharedCheck_6863_ = (!leanh::lean_is_exclusive(v___x_6855_)) as u8;
                    if v_isSharedCheck_6863_ == 0 {
                        v___x_6858_ = v___x_6855_;
                        v_isShared_6859_ = v_isSharedCheck_6863_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6856_);
                        leanh::lean_dec(v___x_6855_);
                        v___x_6858_ = leanh::lean_box(0);
                        v_isShared_6859_ = v_isSharedCheck_6863_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6859_ == 0 {
                    v___x_6861_ = v___x_6858_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6862_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6862_, 0, v_a_6856_);
                    v___x_6861_ = v_reuseFailAlloc_6862_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6861_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___boxed(
    mut v_name_6864_: *mut leanh::LeanObject,
    mut v_bi_6865_: *mut leanh::LeanObject,
    mut v_type_6866_: *mut leanh::LeanObject,
    mut v_k_6867_: *mut leanh::LeanObject,
    mut v_kind_6868_: *mut leanh::LeanObject,
    mut v___y_6869_: *mut leanh::LeanObject,
    mut v___y_6870_: *mut leanh::LeanObject,
    mut v___y_6871_: *mut leanh::LeanObject,
    mut v___y_6872_: *mut leanh::LeanObject,
    mut v___y_6873_: *mut leanh::LeanObject,
    mut v___y_6874_: *mut leanh::LeanObject,
    mut v___y_6875_: *mut leanh::LeanObject,
    mut v___y_6876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_6877_: u8 = 0;
    let mut v_kind_boxed_6878_: u8 = 0;
    let mut v_res_6879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_6877_ = (leanh::lean_unbox(v_bi_6865_) as u8);
    v_kind_boxed_6878_ = (leanh::lean_unbox(v_kind_6868_) as u8);
    v_res_6879_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_6864_, v_bi_boxed_6877_, v_type_6866_, v_k_6867_, v_kind_boxed_6878_, v___y_6869_, v___y_6870_, v___y_6871_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_);
    leanh::lean_dec(v___y_6875_);
    leanh::lean_dec_ref(v___y_6874_);
    leanh::lean_dec(v___y_6873_);
    leanh::lean_dec_ref(v___y_6872_);
    leanh::lean_dec(v___y_6871_);
    leanh::lean_dec(v___y_6870_);
    leanh::lean_dec_ref(v___y_6869_);
    return v_res_6879_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(
    mut v_00_u03b1_6880_: *mut leanh::LeanObject,
    mut v_name_6881_: *mut leanh::LeanObject,
    mut v_bi_6882_: u8,
    mut v_type_6883_: *mut leanh::LeanObject,
    mut v_k_6884_: *mut leanh::LeanObject,
    mut v_kind_6885_: u8,
    mut v___y_6886_: *mut leanh::LeanObject,
    mut v___y_6887_: *mut leanh::LeanObject,
    mut v___y_6888_: *mut leanh::LeanObject,
    mut v___y_6889_: *mut leanh::LeanObject,
    mut v___y_6890_: *mut leanh::LeanObject,
    mut v___y_6891_: *mut leanh::LeanObject,
    mut v___y_6892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6894_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_name_6881_, v_bi_6882_, v_type_6883_, v_k_6884_, v_kind_6885_, v___y_6886_, v___y_6887_, v___y_6888_, v___y_6889_, v___y_6890_, v___y_6891_, v___y_6892_);
    return v___x_6894_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___boxed(
    mut v_00_u03b1_6895_: *mut leanh::LeanObject,
    mut v_name_6896_: *mut leanh::LeanObject,
    mut v_bi_6897_: *mut leanh::LeanObject,
    mut v_type_6898_: *mut leanh::LeanObject,
    mut v_k_6899_: *mut leanh::LeanObject,
    mut v_kind_6900_: *mut leanh::LeanObject,
    mut v___y_6901_: *mut leanh::LeanObject,
    mut v___y_6902_: *mut leanh::LeanObject,
    mut v___y_6903_: *mut leanh::LeanObject,
    mut v___y_6904_: *mut leanh::LeanObject,
    mut v___y_6905_: *mut leanh::LeanObject,
    mut v___y_6906_: *mut leanh::LeanObject,
    mut v___y_6907_: *mut leanh::LeanObject,
    mut v___y_6908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_6909_: u8 = 0;
    let mut v_kind_boxed_6910_: u8 = 0;
    let mut v_res_6911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_6909_ = (leanh::lean_unbox(v_bi_6897_) as u8);
    v_kind_boxed_6910_ = (leanh::lean_unbox(v_kind_6900_) as u8);
    v_res_6911_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0(v_00_u03b1_6895_, v_name_6896_, v_bi_boxed_6909_, v_type_6898_, v_k_6899_, v_kind_boxed_6910_, v___y_6901_, v___y_6902_, v___y_6903_, v___y_6904_, v___y_6905_, v___y_6906_, v___y_6907_);
    leanh::lean_dec(v___y_6907_);
    leanh::lean_dec_ref(v___y_6906_);
    leanh::lean_dec(v___y_6905_);
    leanh::lean_dec_ref(v___y_6904_);
    leanh::lean_dec(v___y_6903_);
    leanh::lean_dec(v___y_6902_);
    leanh::lean_dec_ref(v___y_6901_);
    return v_res_6911_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_extractCore___lam__4(
    mut v_types_6912_: u8,
    mut v_e_6913_: *mut leanh::LeanObject,
    mut v___f_6914_: *mut leanh::LeanObject,
    mut v_____r_6915_: *mut leanh::LeanObject,
    mut v___y_6916_: *mut leanh::LeanObject,
    mut v___y_6917_: *mut leanh::LeanObject,
    mut v___y_6918_: *mut leanh::LeanObject,
    mut v___y_6919_: *mut leanh::LeanObject,
    mut v___y_6920_: *mut leanh::LeanObject,
    mut v___y_6921_: *mut leanh::LeanObject,
    mut v___y_6922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6928_: u8 = 0;
    let mut v___x_6929_: u8 = 0;
    let mut v___x_6930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6935_: u8 = 0;
    let mut v_a_6936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6939_: u8 = 0;
    let mut v___x_6941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6943_: u8 = 0;
    let mut v___x_6944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_types_6912_ == 0 {
                    leanh::lean_inc_ref(v_e_6913_);
                    v___x_6924_ = l_Lean_Meta_isType(
                        v_e_6913_,
                        v___y_6919_,
                        v___y_6920_,
                        v___y_6921_,
                        v___y_6922_,
                    );
                    if leanh::lean_obj_tag(v___x_6924_) == 0 {
                        v_a_6925_ = leanh::lean_ctor_get(v___x_6924_, 0);
                        v_isSharedCheck_6935_ =
                            (!leanh::lean_is_exclusive(v___x_6924_)) as u8;
                        if v_isSharedCheck_6935_ == 0 {
                            v___x_6927_ = v___x_6924_;
                            v_isShared_6928_ = v_isSharedCheck_6935_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6925_);
                            leanh::lean_dec(v___x_6924_);
                            v___x_6927_ = leanh::lean_box(0);
                            v_isShared_6928_ = v_isSharedCheck_6935_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___f_6914_);
                        leanh::lean_dec_ref(v_e_6913_);
                        v_a_6936_ = leanh::lean_ctor_get(v___x_6924_, 0);
                        v_isSharedCheck_6943_ =
                            (!leanh::lean_is_exclusive(v___x_6924_)) as u8;
                        if v_isSharedCheck_6943_ == 0 {
                            v___x_6938_ = v___x_6924_;
                            v_isShared_6939_ = v_isSharedCheck_6943_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6936_);
                            leanh::lean_dec(v___x_6924_);
                            v___x_6938_ = leanh::lean_box(0);
                            v_isShared_6939_ = v_isSharedCheck_6943_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_6913_);
                    v___x_6944_ = leanh::lean_box(0);
                    leanh::lean_inc(v___y_6922_);
                    leanh::lean_inc_ref(v___y_6921_);
                    leanh::lean_inc(v___y_6920_);
                    leanh::lean_inc_ref(v___y_6919_);
                    leanh::lean_inc(v___y_6918_);
                    leanh::lean_inc(v___y_6917_);
                    leanh::lean_inc_ref(v___y_6916_);
                    v___x_6945_ = leanh::lean_apply_9(
                        v___f_6914_,
                        v___x_6944_,
                        v___y_6916_,
                        v___y_6917_,
                        v___y_6918_,
                        v___y_6919_,
                        v___y_6920_,
                        v___y_6921_,
                        v___y_6922_,
                        leanh::lean_box(0),
                    );
                    return v___x_6945_;
                }
            }
            1 => {
                v___x_6929_ = (leanh::lean_unbox(v_a_6925_) as u8);
                leanh::lean_dec(v_a_6925_);
                if v___x_6929_ == 0 {
                    leanh::lean_del_object(v___x_6927_);
                    leanh::lean_dec_ref(v_e_6913_);
                    v___x_6930_ = leanh::lean_box(0);
                    leanh::lean_inc(v___y_6922_);
                    leanh::lean_inc_ref(v___y_6921_);
                    leanh::lean_inc(v___y_6920_);
                    leanh::lean_inc_ref(v___y_6919_);
                    leanh::lean_inc(v___y_6918_);
                    leanh::lean_inc(v___y_6917_);
                    leanh::lean_inc_ref(v___y_6916_);
                    v___x_6931_ = leanh::lean_apply_9(
                        v___f_6914_,
                        v___x_6930_,
                        v___y_6916_,
                        v___y_6917_,
                        v___y_6918_,
                        v___y_6919_,
                        v___y_6920_,
                        v___y_6921_,
                        v___y_6922_,
                        leanh::lean_box(0),
                    );
                    return v___x_6931_;
                } else {
                    leanh::lean_dec_ref(v___f_6914_);
                    if v_isShared_6928_ == 0 {
                        leanh::lean_ctor_set(v___x_6927_, 0, v_e_6913_);
                        v___x_6933_ = v___x_6927_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6934_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6934_, 0, v_e_6913_);
                        v___x_6933_ = v_reuseFailAlloc_6934_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6933_;
            }
            3 => {
                if v_isShared_6939_ == 0 {
                    v___x_6941_ = v___x_6938_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6942_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6942_, 0, v_a_6936_);
                    v___x_6941_ = v_reuseFailAlloc_6942_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6941_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed(
    mut v_types_6946_: *mut leanh::LeanObject,
    mut v_e_6947_: *mut leanh::LeanObject,
    mut v___f_6948_: *mut leanh::LeanObject,
    mut v_____r_6949_: *mut leanh::LeanObject,
    mut v___y_6950_: *mut leanh::LeanObject,
    mut v___y_6951_: *mut leanh::LeanObject,
    mut v___y_6952_: *mut leanh::LeanObject,
    mut v___y_6953_: *mut leanh::LeanObject,
    mut v___y_6954_: *mut leanh::LeanObject,
    mut v___y_6955_: *mut leanh::LeanObject,
    mut v___y_6956_: *mut leanh::LeanObject,
    mut v___y_6957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_types_boxed_6958_: u8 = 0;
    let mut v_res_6959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_types_boxed_6958_ = (leanh::lean_unbox(v_types_6946_) as u8);
    v_res_6959_ = l_Lean_Meta_ExtractLets_extractCore___lam__4(
        v_types_boxed_6958_,
        v_e_6947_,
        v___f_6948_,
        v_____r_6949_,
        v___y_6950_,
        v___y_6951_,
        v___y_6952_,
        v___y_6953_,
        v___y_6954_,
        v___y_6955_,
        v___y_6956_,
    );
    leanh::lean_dec(v___y_6956_);
    leanh::lean_dec_ref(v___y_6955_);
    leanh::lean_dec(v___y_6954_);
    leanh::lean_dec_ref(v___y_6953_);
    leanh::lean_dec(v___y_6952_);
    leanh::lean_dec(v___y_6951_);
    leanh::lean_dec_ref(v___y_6950_);
    return v_res_6959_;
}
pub unsafe fn l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(
    mut v___y_6960_: u8,
    mut v___y_6961_: u8,
) -> u8 {
    if v___y_6960_ == 0 {
        if v___y_6961_ == 0 {
            let mut v___x_6962_: u8 = 0;
            v___x_6962_ = 1;
            return v___x_6962_;
        } else {
            return v___y_6960_;
        }
    } else {
        return v___y_6961_;
    }
}
pub unsafe fn l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed(
    mut v___y_6963_: *mut leanh::LeanObject,
    mut v___y_6964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_50699__boxed_6965_: u8 = 0;
    let mut v___y_50700__boxed_6966_: u8 = 0;
    let mut v_res_6967_: u8 = 0;
    let mut v_r_6968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_50699__boxed_6965_ = (leanh::lean_unbox(v___y_6963_) as u8);
    v___y_50700__boxed_6966_ = (leanh::lean_unbox(v___y_6964_) as u8);
    v_res_6967_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0(
        v___y_50699__boxed_6965_,
        v___y_50700__boxed_6966_,
    );
    v_r_6968_ = leanh::lean_box((v_res_6967_) as usize);
    return v_r_6968_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6969_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_6969_;
}
pub unsafe fn l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(
    mut v_msg_6977_: *mut leanh::LeanObject,
    mut v___y_6978_: *mut leanh::LeanObject,
    mut v___y_6979_: *mut leanh::LeanObject,
    mut v___y_6980_: *mut leanh::LeanObject,
    mut v___y_6981_: *mut leanh::LeanObject,
    mut v___y_6982_: *mut leanh::LeanObject,
    mut v___y_6983_: *mut leanh::LeanObject,
    mut v___y_6984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6992_: u8 = 0;
    let mut v_toFunctor_6993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_6994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_6995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_6996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6999_: u8 = 0;
    let mut v___f_7000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_7013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7016_: u8 = 0;
    let mut v_toFunctor_7017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_7018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_7019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_7020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7023_: u8 = 0;
    let mut v___f_7024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_47587__overap_7048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7052_: u8 = 0;
    let mut v_unused_7053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7054_: u8 = 0;
    let mut v_unused_7055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7058_: u8 = 0;
    let mut v_unused_7059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7060_: u8 = 0;
    let mut v_unused_7061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6986_ = leanh::lean_box(0);
                v___x_6987_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0_once
                    ),
                    _init_l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__0,
                );
                v___x_6988_ = l_StateRefT_x27_instMonad___redArg(v___x_6987_);
                v_toApplicative_6989_ = leanh::lean_ctor_get(v___x_6988_, 0);
                v_isSharedCheck_7060_ = (!leanh::lean_is_exclusive(v___x_6988_)) as u8;
                if v_isSharedCheck_7060_ == 0 {
                    v_unused_7061_ = leanh::lean_ctor_get(v___x_6988_, 1);
                    leanh::lean_dec(v_unused_7061_);
                    v___x_6991_ = v___x_6988_;
                    v_isShared_6992_ = v_isSharedCheck_7060_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_6989_);
                    leanh::lean_dec(v___x_6988_);
                    v___x_6991_ = leanh::lean_box(0);
                    v_isShared_6992_ = v_isSharedCheck_7060_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_6993_ = leanh::lean_ctor_get(v_toApplicative_6989_, 0);
                v_toSeq_6994_ = leanh::lean_ctor_get(v_toApplicative_6989_, 2);
                v_toSeqLeft_6995_ = leanh::lean_ctor_get(v_toApplicative_6989_, 3);
                v_toSeqRight_6996_ = leanh::lean_ctor_get(v_toApplicative_6989_, 4);
                v_isSharedCheck_7058_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_6989_)) as u8;
                if v_isSharedCheck_7058_ == 0 {
                    v_unused_7059_ = leanh::lean_ctor_get(v_toApplicative_6989_, 1);
                    leanh::lean_dec(v_unused_7059_);
                    v___x_6998_ = v_toApplicative_6989_;
                    v_isShared_6999_ = v_isSharedCheck_7058_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_6996_);
                    leanh::lean_inc(v_toSeqLeft_6995_);
                    leanh::lean_inc(v_toSeq_6994_);
                    leanh::lean_inc(v_toFunctor_6993_);
                    leanh::lean_dec(v_toApplicative_6989_);
                    v___x_6998_ = leanh::lean_box(0);
                    v_isShared_6999_ = v_isSharedCheck_7058_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_7000_ =
                    l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__1;
                v___f_7001_ =
                    l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__2;
                leanh::lean_inc_ref(v_toFunctor_6993_);
                v___f_7002_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_7002_, 0, v_toFunctor_6993_);
                v___f_7003_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_7003_, 0, v_toFunctor_6993_);
                v___x_7004_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7004_, 0, v___f_7002_);
                leanh::lean_ctor_set(v___x_7004_, 1, v___f_7003_);
                v___f_7005_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_7005_, 0, v_toSeqRight_6996_);
                v___f_7006_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_7006_, 0, v_toSeqLeft_6995_);
                v___f_7007_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_7007_, 0, v_toSeq_6994_);
                if v_isShared_6999_ == 0 {
                    leanh::lean_ctor_set(v___x_6998_, 4, v___f_7005_);
                    leanh::lean_ctor_set(v___x_6998_, 3, v___f_7006_);
                    leanh::lean_ctor_set(v___x_6998_, 2, v___f_7007_);
                    leanh::lean_ctor_set(v___x_6998_, 1, v___f_7000_);
                    leanh::lean_ctor_set(v___x_6998_, 0, v___x_7004_);
                    v___x_7009_ = v___x_6998_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7057_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7057_, 0, v___x_7004_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7057_, 1, v___f_7000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7057_, 2, v___f_7007_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7057_, 3, v___f_7006_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7057_, 4, v___f_7005_);
                    v___x_7009_ = v_reuseFailAlloc_7057_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6992_ == 0 {
                    leanh::lean_ctor_set(v___x_6991_, 1, v___f_7001_);
                    leanh::lean_ctor_set(v___x_6991_, 0, v___x_7009_);
                    v___x_7011_ = v___x_6991_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7056_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7056_, 0, v___x_7009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7056_, 1, v___f_7001_);
                    v___x_7011_ = v_reuseFailAlloc_7056_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7012_ = l_StateRefT_x27_instMonad___redArg(v___x_7011_);
                v_toApplicative_7013_ = leanh::lean_ctor_get(v___x_7012_, 0);
                v_isSharedCheck_7054_ = (!leanh::lean_is_exclusive(v___x_7012_)) as u8;
                if v_isSharedCheck_7054_ == 0 {
                    v_unused_7055_ = leanh::lean_ctor_get(v___x_7012_, 1);
                    leanh::lean_dec(v_unused_7055_);
                    v___x_7015_ = v___x_7012_;
                    v_isShared_7016_ = v_isSharedCheck_7054_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_7013_);
                    leanh::lean_dec(v___x_7012_);
                    v___x_7015_ = leanh::lean_box(0);
                    v_isShared_7016_ = v_isSharedCheck_7054_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_7017_ = leanh::lean_ctor_get(v_toApplicative_7013_, 0);
                v_toSeq_7018_ = leanh::lean_ctor_get(v_toApplicative_7013_, 2);
                v_toSeqLeft_7019_ = leanh::lean_ctor_get(v_toApplicative_7013_, 3);
                v_toSeqRight_7020_ = leanh::lean_ctor_get(v_toApplicative_7013_, 4);
                v_isSharedCheck_7052_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_7013_)) as u8;
                if v_isSharedCheck_7052_ == 0 {
                    v_unused_7053_ = leanh::lean_ctor_get(v_toApplicative_7013_, 1);
                    leanh::lean_dec(v_unused_7053_);
                    v___x_7022_ = v_toApplicative_7013_;
                    v_isShared_7023_ = v_isSharedCheck_7052_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_7020_);
                    leanh::lean_inc(v_toSeqLeft_7019_);
                    leanh::lean_inc(v_toSeq_7018_);
                    leanh::lean_inc(v_toFunctor_7017_);
                    leanh::lean_dec(v_toApplicative_7013_);
                    v___x_7022_ = leanh::lean_box(0);
                    v_isShared_7023_ = v_isSharedCheck_7052_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_7024_ = leanh::lean_alloc_closure(
                    l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    0,
                );
                v___f_7025_ = leanh::lean_alloc_closure(
                    l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                leanh::lean_closure_set(v___f_7025_, 0, v___f_7024_);
                v___x_7026_ =
                    l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__3;
                v___f_7027_ = leanh::lean_alloc_closure(
                    l_instBEqProd___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___f_7027_, 0, v___f_7025_);
                leanh::lean_closure_set(v___f_7027_, 1, v___x_7026_);
                v___f_7028_ =
                    l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__4;
                v___x_7029_ =
                    l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__5;
                v___f_7030_ = leanh::lean_alloc_closure(
                    l_instHashableProd___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_7030_, 0, v___f_7028_);
                leanh::lean_closure_set(v___f_7030_, 1, v___x_7029_);
                v___f_7031_ =
                    l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__6;
                v___f_7032_ =
                    l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___closed__7;
                leanh::lean_inc_ref(v_toFunctor_7017_);
                v___f_7033_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_7033_, 0, v_toFunctor_7017_);
                v___f_7034_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_7034_, 0, v_toFunctor_7017_);
                v___x_7035_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7035_, 0, v___f_7033_);
                leanh::lean_ctor_set(v___x_7035_, 1, v___f_7034_);
                v___f_7036_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_7036_, 0, v_toSeqRight_7020_);
                v___f_7037_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_7037_, 0, v_toSeqLeft_7019_);
                v___f_7038_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_7038_, 0, v_toSeq_7018_);
                if v_isShared_7023_ == 0 {
                    leanh::lean_ctor_set(v___x_7022_, 4, v___f_7036_);
                    leanh::lean_ctor_set(v___x_7022_, 3, v___f_7037_);
                    leanh::lean_ctor_set(v___x_7022_, 2, v___f_7038_);
                    leanh::lean_ctor_set(v___x_7022_, 1, v___f_7031_);
                    leanh::lean_ctor_set(v___x_7022_, 0, v___x_7035_);
                    v___x_7040_ = v___x_7022_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7051_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7051_, 0, v___x_7035_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7051_, 1, v___f_7031_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7051_, 2, v___f_7038_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7051_, 3, v___f_7037_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7051_, 4, v___f_7036_);
                    v___x_7040_ = v_reuseFailAlloc_7051_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_7016_ == 0 {
                    leanh::lean_ctor_set(v___x_7015_, 1, v___f_7032_);
                    leanh::lean_ctor_set(v___x_7015_, 0, v___x_7040_);
                    v___x_7042_ = v___x_7015_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7050_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7050_, 0, v___x_7040_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7050_, 1, v___f_7032_);
                    v___x_7042_ = v_reuseFailAlloc_7050_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_7043_ = l_StateRefT_x27_instMonad___redArg(v___x_7042_);
                v___x_7044_ = l_Lean_MonadCacheT_instMonad___redArg(
                    v___x_6986_,
                    v___f_7027_,
                    v___f_7030_,
                    v___x_7043_,
                );
                v___x_7045_ = l_Lean_instInhabitedExpr;
                v___x_7046_ = l_instInhabitedOfMonad___redArg(v___x_7044_, v___x_7045_);
                v___f_7047_ = leanh::lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_7047_, 0, v___x_7046_);
                v___x_47587__overap_7048_ = lean_panic_fn_borrowed(v___f_7047_, v_msg_6977_);
                leanh::lean_dec_ref(v___f_7047_);
                leanh::lean_inc(v___y_6984_);
                leanh::lean_inc_ref(v___y_6983_);
                leanh::lean_inc(v___y_6982_);
                leanh::lean_inc_ref(v___y_6981_);
                leanh::lean_inc(v___y_6980_);
                leanh::lean_inc(v___y_6979_);
                leanh::lean_inc_ref(v___y_6978_);
                v___x_7049_ = leanh::lean_apply_8(
                    v___x_47587__overap_7048_,
                    v___y_6978_,
                    v___y_6979_,
                    v___y_6980_,
                    v___y_6981_,
                    v___y_6982_,
                    v___y_6983_,
                    v___y_6984_,
                    leanh::lean_box(0),
                );
                return v___x_7049_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4___boxed(
    mut v_msg_7062_: *mut leanh::LeanObject,
    mut v___y_7063_: *mut leanh::LeanObject,
    mut v___y_7064_: *mut leanh::LeanObject,
    mut v___y_7065_: *mut leanh::LeanObject,
    mut v___y_7066_: *mut leanh::LeanObject,
    mut v___y_7067_: *mut leanh::LeanObject,
    mut v___y_7068_: *mut leanh::LeanObject,
    mut v___y_7069_: *mut leanh::LeanObject,
    mut v___y_7070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7071_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(
        v_msg_7062_,
        v___y_7063_,
        v___y_7064_,
        v___y_7065_,
        v___y_7066_,
        v___y_7067_,
        v___y_7068_,
        v___y_7069_,
    );
    leanh::lean_dec(v___y_7069_);
    leanh::lean_dec_ref(v___y_7068_);
    leanh::lean_dec(v___y_7067_);
    leanh::lean_dec_ref(v___y_7066_);
    leanh::lean_dec(v___y_7065_);
    leanh::lean_dec(v___y_7064_);
    leanh::lean_dec_ref(v___y_7063_);
    return v_res_7071_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_extractCore___lam__0(
    mut v_binderName_7072_: *mut leanh::LeanObject,
    mut v_binderInfo_7073_: u8,
    mut v_e_7074_: *mut leanh::LeanObject,
    mut v_binderType_7075_: *mut leanh::LeanObject,
    mut v_body_7076_: *mut leanh::LeanObject,
    mut v_t_7077_: *mut leanh::LeanObject,
    mut v_b_7078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_7080_: u8 = 0;
    let mut v___x_7081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: u8 = 0;
    let mut v___x_7083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7084_: usize = 0;
    let mut v___x_7085_: usize = 0;
    let mut v___x_7086_: u8 = 0;
    let mut v___x_7087_: usize = 0;
    let mut v___x_7088_: usize = 0;
    let mut v___x_7089_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7084_ = lean_ptr_addr(v_binderType_7075_);
                v___x_7085_ = lean_ptr_addr(v_t_7077_);
                v___x_7086_ = lean_usize_dec_eq(v___x_7084_, v___x_7085_);
                if v___x_7086_ == 0 {
                    v___y_7080_ = v___x_7086_;
                    state = 1;
                    continue;
                } else {
                    v___x_7087_ = lean_ptr_addr(v_body_7076_);
                    v___x_7088_ = lean_ptr_addr(v_b_7078_);
                    v___x_7089_ = lean_usize_dec_eq(v___x_7087_, v___x_7088_);
                    v___y_7080_ = v___x_7089_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_7080_ == 0 {
                    v___x_7081_ = l_Lean_Expr_lam___override(
                        v_binderName_7072_,
                        v_t_7077_,
                        v_b_7078_,
                        v_binderInfo_7073_,
                    );
                    return v___x_7081_;
                } else {
                    v___x_7082_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_7073_, v_binderInfo_7073_);
                    if v___x_7082_ == 0 {
                        v___x_7083_ = l_Lean_Expr_lam___override(
                            v_binderName_7072_,
                            v_t_7077_,
                            v_b_7078_,
                            v_binderInfo_7073_,
                        );
                        return v___x_7083_;
                    } else {
                        leanh::lean_dec_ref(v_b_7078_);
                        leanh::lean_dec_ref(v_t_7077_);
                        leanh::lean_dec(v_binderName_7072_);
                        leanh::lean_inc_ref(v_e_7074_);
                        return v_e_7074_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed(
    mut v_binderName_7090_: *mut leanh::LeanObject,
    mut v_binderInfo_7091_: *mut leanh::LeanObject,
    mut v_e_7092_: *mut leanh::LeanObject,
    mut v_binderType_7093_: *mut leanh::LeanObject,
    mut v_body_7094_: *mut leanh::LeanObject,
    mut v_t_7095_: *mut leanh::LeanObject,
    mut v_b_7096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderInfo_50886__boxed_7097_: u8 = 0;
    let mut v_res_7098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_50886__boxed_7097_ = (leanh::lean_unbox(v_binderInfo_7091_) as u8);
    v_res_7098_ = l_Lean_Meta_ExtractLets_extractCore___lam__0(
        v_binderName_7090_,
        v_binderInfo_50886__boxed_7097_,
        v_e_7092_,
        v_binderType_7093_,
        v_body_7094_,
        v_t_7095_,
        v_b_7096_,
    );
    leanh::lean_dec_ref(v_body_7094_);
    leanh::lean_dec_ref(v_binderType_7093_);
    leanh::lean_dec_ref(v_e_7092_);
    return v_res_7098_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_extractCore___lam__1(
    mut v_binderName_7099_: *mut leanh::LeanObject,
    mut v_binderInfo_7100_: u8,
    mut v_e_7101_: *mut leanh::LeanObject,
    mut v_binderType_7102_: *mut leanh::LeanObject,
    mut v_body_7103_: *mut leanh::LeanObject,
    mut v_t_7104_: *mut leanh::LeanObject,
    mut v_b_7105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_7107_: u8 = 0;
    let mut v___x_7108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7109_: u8 = 0;
    let mut v___x_7110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7111_: usize = 0;
    let mut v___x_7112_: usize = 0;
    let mut v___x_7113_: u8 = 0;
    let mut v___x_7114_: usize = 0;
    let mut v___x_7115_: usize = 0;
    let mut v___x_7116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7111_ = lean_ptr_addr(v_binderType_7102_);
                v___x_7112_ = lean_ptr_addr(v_t_7104_);
                v___x_7113_ = lean_usize_dec_eq(v___x_7111_, v___x_7112_);
                if v___x_7113_ == 0 {
                    v___y_7107_ = v___x_7113_;
                    state = 1;
                    continue;
                } else {
                    v___x_7114_ = lean_ptr_addr(v_body_7103_);
                    v___x_7115_ = lean_ptr_addr(v_b_7105_);
                    v___x_7116_ = lean_usize_dec_eq(v___x_7114_, v___x_7115_);
                    v___y_7107_ = v___x_7116_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_7107_ == 0 {
                    v___x_7108_ = l_Lean_Expr_forallE___override(
                        v_binderName_7099_,
                        v_t_7104_,
                        v_b_7105_,
                        v_binderInfo_7100_,
                    );
                    return v___x_7108_;
                } else {
                    v___x_7109_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_7100_, v_binderInfo_7100_);
                    if v___x_7109_ == 0 {
                        v___x_7110_ = l_Lean_Expr_forallE___override(
                            v_binderName_7099_,
                            v_t_7104_,
                            v_b_7105_,
                            v_binderInfo_7100_,
                        );
                        return v___x_7110_;
                    } else {
                        leanh::lean_dec_ref(v_b_7105_);
                        leanh::lean_dec_ref(v_t_7104_);
                        leanh::lean_dec(v_binderName_7099_);
                        leanh::lean_inc_ref(v_e_7101_);
                        return v_e_7101_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed(
    mut v_binderName_7117_: *mut leanh::LeanObject,
    mut v_binderInfo_7118_: *mut leanh::LeanObject,
    mut v_e_7119_: *mut leanh::LeanObject,
    mut v_binderType_7120_: *mut leanh::LeanObject,
    mut v_body_7121_: *mut leanh::LeanObject,
    mut v_t_7122_: *mut leanh::LeanObject,
    mut v_b_7123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderInfo_50920__boxed_7124_: u8 = 0;
    let mut v_res_7125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_50920__boxed_7124_ = (leanh::lean_unbox(v_binderInfo_7118_) as u8);
    v_res_7125_ = l_Lean_Meta_ExtractLets_extractCore___lam__1(
        v_binderName_7117_,
        v_binderInfo_50920__boxed_7124_,
        v_e_7119_,
        v_binderType_7120_,
        v_body_7121_,
        v_t_7122_,
        v_b_7123_,
    );
    leanh::lean_dec_ref(v_body_7121_);
    leanh::lean_dec_ref(v_binderType_7120_);
    leanh::lean_dec_ref(v_e_7119_);
    return v_res_7125_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(
    mut v_name_7126_: *mut leanh::LeanObject,
    mut v_type_7127_: *mut leanh::LeanObject,
    mut v_val_7128_: *mut leanh::LeanObject,
    mut v_k_7129_: *mut leanh::LeanObject,
    mut v_nondep_7130_: u8,
    mut v_kind_7131_: u8,
    mut v___y_7132_: *mut leanh::LeanObject,
    mut v___y_7133_: *mut leanh::LeanObject,
    mut v___y_7134_: *mut leanh::LeanObject,
    mut v___y_7135_: *mut leanh::LeanObject,
    mut v___y_7136_: *mut leanh::LeanObject,
    mut v___y_7137_: *mut leanh::LeanObject,
    mut v___y_7138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7145_: u8 = 0;
    let mut v___x_7147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_7134_);
                leanh::lean_inc(v___y_7133_);
                leanh::lean_inc_ref(v___y_7132_);
                v___f_7140_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                leanh::lean_closure_set(v___f_7140_, 0, v_k_7129_);
                leanh::lean_closure_set(v___f_7140_, 1, v___y_7132_);
                leanh::lean_closure_set(v___f_7140_, 2, v___y_7133_);
                leanh::lean_closure_set(v___f_7140_, 3, v___y_7134_);
                v___x_7141_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    leanh::lean_box(0),
                    v_name_7126_,
                    v_type_7127_,
                    v_val_7128_,
                    v___f_7140_,
                    v_nondep_7130_,
                    v_kind_7131_,
                    v___y_7135_,
                    v___y_7136_,
                    v___y_7137_,
                    v___y_7138_,
                );
                if leanh::lean_obj_tag(v___x_7141_) == 0 {
                    return v___x_7141_;
                } else {
                    v_a_7142_ = leanh::lean_ctor_get(v___x_7141_, 0);
                    v_isSharedCheck_7149_ = (!leanh::lean_is_exclusive(v___x_7141_)) as u8;
                    if v_isSharedCheck_7149_ == 0 {
                        v___x_7144_ = v___x_7141_;
                        v_isShared_7145_ = v_isSharedCheck_7149_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7142_);
                        leanh::lean_dec(v___x_7141_);
                        v___x_7144_ = leanh::lean_box(0);
                        v_isShared_7145_ = v_isSharedCheck_7149_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7145_ == 0 {
                    v___x_7147_ = v___x_7144_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7148_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7148_, 0, v_a_7142_);
                    v___x_7147_ = v_reuseFailAlloc_7148_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg___boxed(
    mut v_name_7150_: *mut leanh::LeanObject,
    mut v_type_7151_: *mut leanh::LeanObject,
    mut v_val_7152_: *mut leanh::LeanObject,
    mut v_k_7153_: *mut leanh::LeanObject,
    mut v_nondep_7154_: *mut leanh::LeanObject,
    mut v_kind_7155_: *mut leanh::LeanObject,
    mut v___y_7156_: *mut leanh::LeanObject,
    mut v___y_7157_: *mut leanh::LeanObject,
    mut v___y_7158_: *mut leanh::LeanObject,
    mut v___y_7159_: *mut leanh::LeanObject,
    mut v___y_7160_: *mut leanh::LeanObject,
    mut v___y_7161_: *mut leanh::LeanObject,
    mut v___y_7162_: *mut leanh::LeanObject,
    mut v___y_7163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_boxed_7164_: u8 = 0;
    let mut v_kind_boxed_7165_: u8 = 0;
    let mut v_res_7166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_7164_ = (leanh::lean_unbox(v_nondep_7154_) as u8);
    v_kind_boxed_7165_ = (leanh::lean_unbox(v_kind_7155_) as u8);
    v_res_7166_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_7150_, v_type_7151_, v_val_7152_, v_k_7153_, v_nondep_boxed_7164_, v_kind_boxed_7165_, v___y_7156_, v___y_7157_, v___y_7158_, v___y_7159_, v___y_7160_, v___y_7161_, v___y_7162_);
    leanh::lean_dec(v___y_7162_);
    leanh::lean_dec_ref(v___y_7161_);
    leanh::lean_dec(v___y_7160_);
    leanh::lean_dec_ref(v___y_7159_);
    leanh::lean_dec(v___y_7158_);
    leanh::lean_dec(v___y_7157_);
    leanh::lean_dec_ref(v___y_7156_);
    return v_res_7166_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(
    mut v_msg_7167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7168_ = l_Lean_instInhabitedExpr;
    v___x_7169_ = lean_panic_fn_borrowed(v___x_7168_, v_msg_7167_);
    return v___x_7169_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(
    mut v_a_7170_: *mut leanh::LeanObject,
    mut v_x_7171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_7173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7176_: u8 = 0;
    let mut v___x_7178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7171_) == 0 {
                    v___x_7172_ = leanh::lean_box(0);
                    return v___x_7172_;
                } else {
                    v_key_7173_ = leanh::lean_ctor_get(v_x_7171_, 0);
                    v_value_7174_ = leanh::lean_ctor_get(v_x_7171_, 1);
                    v_tail_7175_ = leanh::lean_ctor_get(v_x_7171_, 2);
                    v___x_7176_ = l_Lean_ExprStructEq_beq(v_key_7173_, v_a_7170_);
                    if v___x_7176_ == 0 {
                        v_x_7171_ = v_tail_7175_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_7174_);
                        v___x_7178_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_7178_, 0, v_value_7174_);
                        return v___x_7178_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg___boxed(
    mut v_a_7179_: *mut leanh::LeanObject,
    mut v_x_7180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7181_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_7179_, v_x_7180_);
    leanh::lean_dec(v_x_7180_);
    leanh::lean_dec_ref(v_a_7179_);
    return v_res_7181_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(
    mut v_m_7182_: *mut leanh::LeanObject,
    mut v_a_7183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_7184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7186_: u64 = 0;
    let mut v___x_7187_: u64 = 0;
    let mut v___x_7188_: u64 = 0;
    let mut v_fold_7189_: u64 = 0;
    let mut v___x_7190_: u64 = 0;
    let mut v___x_7191_: u64 = 0;
    let mut v___x_7192_: u64 = 0;
    let mut v___x_7193_: usize = 0;
    let mut v___x_7194_: usize = 0;
    let mut v___x_7195_: usize = 0;
    let mut v___x_7196_: usize = 0;
    let mut v___x_7197_: usize = 0;
    let mut v___x_7198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_7184_ = leanh::lean_ctor_get(v_m_7182_, 1);
    v___x_7185_ = lean_array_get_size(v_buckets_7184_);
    v___x_7186_ = l_Lean_ExprStructEq_hash(v_a_7183_);
    v___x_7187_ = 32u64;
    v___x_7188_ = lean_uint64_shift_right(v___x_7186_, v___x_7187_);
    v_fold_7189_ = lean_uint64_xor(v___x_7186_, v___x_7188_);
    v___x_7190_ = 16u64;
    v___x_7191_ = lean_uint64_shift_right(v_fold_7189_, v___x_7190_);
    v___x_7192_ = lean_uint64_xor(v_fold_7189_, v___x_7191_);
    v___x_7193_ = lean_uint64_to_usize(v___x_7192_);
    v___x_7194_ = lean_usize_of_nat(v___x_7185_);
    v___x_7195_ = 1usize;
    v___x_7196_ = lean_usize_sub(v___x_7194_, v___x_7195_);
    v___x_7197_ = lean_usize_land(v___x_7193_, v___x_7196_);
    v___x_7198_ = lean_array_uget_borrowed(v_buckets_7184_, v___x_7197_);
    v___x_7199_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_7183_, v___x_7198_);
    return v___x_7199_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg___boxed(
    mut v_m_7200_: *mut leanh::LeanObject,
    mut v_a_7201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7202_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_7200_, v_a_7201_);
    leanh::lean_dec_ref(v_a_7201_);
    leanh::lean_dec_ref(v_m_7200_);
    return v_res_7202_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(
    mut v_a_7203_: *mut leanh::LeanObject,
    mut v_x_7204_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_7205_: u8 = 0;
    let mut v_key_7206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7213_: u8 = 0;
    let mut v___x_7215_: u8 = 0;
    let mut v___x_7216_: u8 = 0;
    let mut v___x_7218_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7204_) == 0 {
                    v___x_7205_ = 0;
                    return v___x_7205_;
                } else {
                    v_key_7206_ = leanh::lean_ctor_get(v_x_7204_, 0);
                    v_tail_7207_ = leanh::lean_ctor_get(v_x_7204_, 2);
                    v_fst_7208_ = leanh::lean_ctor_get(v_key_7206_, 0);
                    v_snd_7209_ = leanh::lean_ctor_get(v_key_7206_, 1);
                    v_fst_7210_ = leanh::lean_ctor_get(v_a_7203_, 0);
                    v_snd_7211_ = leanh::lean_ctor_get(v_a_7203_, 1);
                    v___x_7215_ = (leanh::lean_unbox(v_fst_7208_) as u8);
                    if v___x_7215_ == 0 {
                        v___x_7216_ = (leanh::lean_unbox(v_fst_7210_) as u8);
                        if v___x_7216_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v_x_7204_ = v_tail_7207_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_7218_ = (leanh::lean_unbox(v_fst_7210_) as u8);
                        if v___x_7218_ == 0 {
                            v_x_7204_ = v_tail_7207_;
                            state = 0;
                            continue;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7213_ = l_Lean_ExprStructEq_beq(v_snd_7209_, v_snd_7211_);
                if v___x_7213_ == 0 {
                    v_x_7204_ = v_tail_7207_;
                    state = 0;
                    continue;
                } else {
                    return v___x_7213_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg___boxed(
    mut v_a_7220_: *mut leanh::LeanObject,
    mut v_x_7221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7222_: u8 = 0;
    let mut v_r_7223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7222_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_7220_, v_x_7221_);
    leanh::lean_dec(v_x_7221_);
    leanh::lean_dec_ref(v_a_7220_);
    v_r_7223_ = leanh::lean_box((v_res_7222_) as usize);
    return v_r_7223_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(
    mut v_a_7224_: *mut leanh::LeanObject,
    mut v_b_7225_: *mut leanh::LeanObject,
    mut v_x_7226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_7227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7232_: u8 = 0;
    let mut v___x_7234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7243_: u8 = 0;
    let mut v___x_7244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: u8 = 0;
    let mut v___x_7246_: u8 = 0;
    let mut v___x_7247_: u8 = 0;
    let mut v_isSharedCheck_7248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7226_) == 0 {
                    leanh::lean_dec(v_b_7225_);
                    leanh::lean_dec_ref(v_a_7224_);
                    return v_x_7226_;
                } else {
                    v_key_7227_ = leanh::lean_ctor_get(v_x_7226_, 0);
                    v_value_7228_ = leanh::lean_ctor_get(v_x_7226_, 1);
                    v_tail_7229_ = leanh::lean_ctor_get(v_x_7226_, 2);
                    v_isSharedCheck_7248_ = (!leanh::lean_is_exclusive(v_x_7226_)) as u8;
                    if v_isSharedCheck_7248_ == 0 {
                        v___x_7231_ = v_x_7226_;
                        v_isShared_7232_ = v_isSharedCheck_7248_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_7229_);
                        leanh::lean_inc(v_value_7228_);
                        leanh::lean_inc(v_key_7227_);
                        leanh::lean_dec(v_x_7226_);
                        v___x_7231_ = leanh::lean_box(0);
                        v_isShared_7232_ = v_isSharedCheck_7248_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_7238_ = leanh::lean_ctor_get(v_key_7227_, 0);
                v_snd_7239_ = leanh::lean_ctor_get(v_key_7227_, 1);
                v_fst_7240_ = leanh::lean_ctor_get(v_a_7224_, 0);
                v_snd_7241_ = leanh::lean_ctor_get(v_a_7224_, 1);
                v___x_7245_ = (leanh::lean_unbox(v_fst_7238_) as u8);
                if v___x_7245_ == 0 {
                    v___x_7246_ = (leanh::lean_unbox(v_fst_7240_) as u8);
                    if v___x_7246_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_7247_ = (leanh::lean_unbox(v_fst_7240_) as u8);
                    if v___x_7247_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_7234_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_7224_, v_b_7225_, v_tail_7229_);
                if v_isShared_7232_ == 0 {
                    leanh::lean_ctor_set(v___x_7231_, 2, v___x_7234_);
                    v___x_7236_ = v___x_7231_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7237_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7237_, 0, v_key_7227_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7237_, 1, v_value_7228_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7237_, 2, v___x_7234_);
                    v___x_7236_ = v_reuseFailAlloc_7237_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7236_;
            }
            4 => {
                v___x_7243_ = l_Lean_ExprStructEq_beq(v_snd_7239_, v_snd_7241_);
                if v___x_7243_ == 0 {
                    state = 2;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_7231_);
                    leanh::lean_dec(v_value_7228_);
                    leanh::lean_dec(v_key_7227_);
                    v___x_7244_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_7244_, 0, v_a_7224_);
                    leanh::lean_ctor_set(v___x_7244_, 1, v_b_7225_);
                    leanh::lean_ctor_set(v___x_7244_, 2, v_tail_7229_);
                    return v___x_7244_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(
    mut v_x_7249_: *mut leanh::LeanObject,
    mut v_x_7250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_7251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7256_: u8 = 0;
    let mut v_fst_7257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7261_: u64 = 0;
    let mut v___x_7262_: u64 = 0;
    let mut v___x_7263_: u64 = 0;
    let mut v___x_7264_: u64 = 0;
    let mut v___x_7265_: u64 = 0;
    let mut v_fold_7266_: u64 = 0;
    let mut v___x_7267_: u64 = 0;
    let mut v___x_7268_: u64 = 0;
    let mut v___x_7269_: u64 = 0;
    let mut v___x_7270_: usize = 0;
    let mut v___x_7271_: usize = 0;
    let mut v___x_7272_: usize = 0;
    let mut v___x_7273_: usize = 0;
    let mut v___x_7274_: usize = 0;
    let mut v___x_7275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7281_: u8 = 0;
    let mut v___x_7282_: u64 = 0;
    let mut v___x_7283_: u64 = 0;
    let mut v_isSharedCheck_7284_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7250_) == 0 {
                    return v_x_7249_;
                } else {
                    v_key_7251_ = leanh::lean_ctor_get(v_x_7250_, 0);
                    v_value_7252_ = leanh::lean_ctor_get(v_x_7250_, 1);
                    v_tail_7253_ = leanh::lean_ctor_get(v_x_7250_, 2);
                    v_isSharedCheck_7284_ = (!leanh::lean_is_exclusive(v_x_7250_)) as u8;
                    if v_isSharedCheck_7284_ == 0 {
                        v___x_7255_ = v_x_7250_;
                        v_isShared_7256_ = v_isSharedCheck_7284_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_7253_);
                        leanh::lean_inc(v_value_7252_);
                        leanh::lean_inc(v_key_7251_);
                        leanh::lean_dec(v_x_7250_);
                        v___x_7255_ = leanh::lean_box(0);
                        v_isShared_7256_ = v_isSharedCheck_7284_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_7257_ = leanh::lean_ctor_get(v_key_7251_, 0);
                v_snd_7258_ = leanh::lean_ctor_get(v_key_7251_, 1);
                v___x_7259_ = lean_array_get_size(v_x_7249_);
                v___x_7281_ = (leanh::lean_unbox(v_fst_7257_) as u8);
                if v___x_7281_ == 0 {
                    v___x_7282_ = 13u64;
                    v___y_7261_ = v___x_7282_;
                    state = 2;
                    continue;
                } else {
                    v___x_7283_ = 11u64;
                    v___y_7261_ = v___x_7283_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7262_ = l_Lean_ExprStructEq_hash(v_snd_7258_);
                v___x_7263_ = lean_uint64_mix_hash(v___y_7261_, v___x_7262_);
                v___x_7264_ = 32u64;
                v___x_7265_ = lean_uint64_shift_right(v___x_7263_, v___x_7264_);
                v_fold_7266_ = lean_uint64_xor(v___x_7263_, v___x_7265_);
                v___x_7267_ = 16u64;
                v___x_7268_ = lean_uint64_shift_right(v_fold_7266_, v___x_7267_);
                v___x_7269_ = lean_uint64_xor(v_fold_7266_, v___x_7268_);
                v___x_7270_ = lean_uint64_to_usize(v___x_7269_);
                v___x_7271_ = lean_usize_of_nat(v___x_7259_);
                v___x_7272_ = 1usize;
                v___x_7273_ = lean_usize_sub(v___x_7271_, v___x_7272_);
                v___x_7274_ = lean_usize_land(v___x_7270_, v___x_7273_);
                v___x_7275_ = lean_array_uget_borrowed(v_x_7249_, v___x_7274_);
                leanh::lean_inc(v___x_7275_);
                if v_isShared_7256_ == 0 {
                    leanh::lean_ctor_set(v___x_7255_, 2, v___x_7275_);
                    v___x_7277_ = v___x_7255_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7280_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7280_, 0, v_key_7251_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7280_, 1, v_value_7252_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7280_, 2, v___x_7275_);
                    v___x_7277_ = v_reuseFailAlloc_7280_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7278_ = lean_array_uset(v_x_7249_, v___x_7274_, v___x_7277_);
                v_x_7249_ = v___x_7278_;
                v_x_7250_ = v_tail_7253_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(
    mut v_i_7285_: *mut leanh::LeanObject,
    mut v_source_7286_: *mut leanh::LeanObject,
    mut v_target_7287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7289_: u8 = 0;
    let mut v_es_7290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_7292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_7293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7288_ = lean_array_get_size(v_source_7286_);
                v___x_7289_ = lean_nat_dec_lt(v_i_7285_, v___x_7288_);
                if v___x_7289_ == 0 {
                    leanh::lean_dec_ref(v_source_7286_);
                    leanh::lean_dec(v_i_7285_);
                    return v_target_7287_;
                } else {
                    v_es_7290_ = lean_array_fget(v_source_7286_, v_i_7285_);
                    v___x_7291_ = leanh::lean_box(0);
                    v_source_7292_ = lean_array_fset(v_source_7286_, v_i_7285_, v___x_7291_);
                    v_target_7293_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_target_7287_, v_es_7290_);
                    v___x_7294_ = leanh::lean_unsigned_to_nat(1);
                    v___x_7295_ = lean_nat_add(v_i_7285_, v___x_7294_);
                    leanh::lean_dec(v_i_7285_);
                    v_i_7285_ = v___x_7295_;
                    v_source_7286_ = v_source_7292_;
                    v_target_7287_ = v_target_7293_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(
    mut v_data_7297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_7300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7298_ = lean_array_get_size(v_data_7297_);
    v___x_7299_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_7300_ = lean_nat_mul(v___x_7298_, v___x_7299_);
    v___x_7301_ = leanh::lean_unsigned_to_nat(0);
    v___x_7302_ = leanh::lean_box(0);
    v___x_7303_ = lean_mk_array(v_nbuckets_7300_, v___x_7302_);
    v___x_7304_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v___x_7301_, v_data_7297_, v___x_7303_);
    return v___x_7304_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(
    mut v_m_7305_: *mut leanh::LeanObject,
    mut v_a_7306_: *mut leanh::LeanObject,
    mut v_b_7307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_7308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_7309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7312_: u8 = 0;
    let mut v_fst_7313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7317_: u64 = 0;
    let mut v___x_7318_: u64 = 0;
    let mut v___x_7319_: u64 = 0;
    let mut v___x_7320_: u64 = 0;
    let mut v___x_7321_: u64 = 0;
    let mut v_fold_7322_: u64 = 0;
    let mut v___x_7323_: u64 = 0;
    let mut v___x_7324_: u64 = 0;
    let mut v___x_7325_: u64 = 0;
    let mut v___x_7326_: usize = 0;
    let mut v___x_7327_: usize = 0;
    let mut v___x_7328_: usize = 0;
    let mut v___x_7329_: usize = 0;
    let mut v___x_7330_: usize = 0;
    let mut v_bkt_7331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7332_: u8 = 0;
    let mut v___x_7333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_7334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_7336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7342_: u8 = 0;
    let mut v_val_7343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_7351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7357_: u8 = 0;
    let mut v___x_7358_: u64 = 0;
    let mut v___x_7359_: u64 = 0;
    let mut v_isSharedCheck_7360_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_7308_ = leanh::lean_ctor_get(v_m_7305_, 0);
                v_buckets_7309_ = leanh::lean_ctor_get(v_m_7305_, 1);
                v_isSharedCheck_7360_ = (!leanh::lean_is_exclusive(v_m_7305_)) as u8;
                if v_isSharedCheck_7360_ == 0 {
                    v___x_7311_ = v_m_7305_;
                    v_isShared_7312_ = v_isSharedCheck_7360_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_7309_);
                    leanh::lean_inc(v_size_7308_);
                    leanh::lean_dec(v_m_7305_);
                    v___x_7311_ = leanh::lean_box(0);
                    v_isShared_7312_ = v_isSharedCheck_7360_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_7313_ = leanh::lean_ctor_get(v_a_7306_, 0);
                v_snd_7314_ = leanh::lean_ctor_get(v_a_7306_, 1);
                v___x_7315_ = lean_array_get_size(v_buckets_7309_);
                v___x_7357_ = (leanh::lean_unbox(v_fst_7313_) as u8);
                if v___x_7357_ == 0 {
                    v___x_7358_ = 13u64;
                    v___y_7317_ = v___x_7358_;
                    state = 2;
                    continue;
                } else {
                    v___x_7359_ = 11u64;
                    v___y_7317_ = v___x_7359_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7318_ = l_Lean_ExprStructEq_hash(v_snd_7314_);
                v___x_7319_ = lean_uint64_mix_hash(v___y_7317_, v___x_7318_);
                v___x_7320_ = 32u64;
                v___x_7321_ = lean_uint64_shift_right(v___x_7319_, v___x_7320_);
                v_fold_7322_ = lean_uint64_xor(v___x_7319_, v___x_7321_);
                v___x_7323_ = 16u64;
                v___x_7324_ = lean_uint64_shift_right(v_fold_7322_, v___x_7323_);
                v___x_7325_ = lean_uint64_xor(v_fold_7322_, v___x_7324_);
                v___x_7326_ = lean_uint64_to_usize(v___x_7325_);
                v___x_7327_ = lean_usize_of_nat(v___x_7315_);
                v___x_7328_ = 1usize;
                v___x_7329_ = lean_usize_sub(v___x_7327_, v___x_7328_);
                v___x_7330_ = lean_usize_land(v___x_7326_, v___x_7329_);
                v_bkt_7331_ = lean_array_uget_borrowed(v_buckets_7309_, v___x_7330_);
                v___x_7332_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_7306_, v_bkt_7331_);
                if v___x_7332_ == 0 {
                    v___x_7333_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_7334_ = lean_nat_add(v_size_7308_, v___x_7333_);
                    leanh::lean_dec(v_size_7308_);
                    leanh::lean_inc(v_bkt_7331_);
                    v___x_7335_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_7335_, 0, v_a_7306_);
                    leanh::lean_ctor_set(v___x_7335_, 1, v_b_7307_);
                    leanh::lean_ctor_set(v___x_7335_, 2, v_bkt_7331_);
                    v_buckets_x27_7336_ =
                        lean_array_uset(v_buckets_7309_, v___x_7330_, v___x_7335_);
                    v___x_7337_ = leanh::lean_unsigned_to_nat(4);
                    v___x_7338_ = lean_nat_mul(v_size_x27_7334_, v___x_7337_);
                    v___x_7339_ = leanh::lean_unsigned_to_nat(3);
                    v___x_7340_ = lean_nat_div(v___x_7338_, v___x_7339_);
                    leanh::lean_dec(v___x_7338_);
                    v___x_7341_ = lean_array_get_size(v_buckets_x27_7336_);
                    v___x_7342_ = lean_nat_dec_le(v___x_7340_, v___x_7341_);
                    leanh::lean_dec(v___x_7340_);
                    if v___x_7342_ == 0 {
                        v_val_7343_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_buckets_x27_7336_);
                        if v_isShared_7312_ == 0 {
                            leanh::lean_ctor_set(v___x_7311_, 1, v_val_7343_);
                            leanh::lean_ctor_set(v___x_7311_, 0, v_size_x27_7334_);
                            v___x_7345_ = v___x_7311_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_7346_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_7346_,
                                0,
                                v_size_x27_7334_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_7346_, 1, v_val_7343_);
                            v___x_7345_ = v_reuseFailAlloc_7346_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_7312_ == 0 {
                            leanh::lean_ctor_set(v___x_7311_, 1, v_buckets_x27_7336_);
                            leanh::lean_ctor_set(v___x_7311_, 0, v_size_x27_7334_);
                            v___x_7348_ = v___x_7311_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_7349_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_7349_,
                                0,
                                v_size_x27_7334_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_7349_,
                                1,
                                v_buckets_x27_7336_,
                            );
                            v___x_7348_ = v_reuseFailAlloc_7349_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_7331_);
                    v___x_7350_ = leanh::lean_box(0);
                    v_buckets_x27_7351_ =
                        lean_array_uset(v_buckets_7309_, v___x_7330_, v___x_7350_);
                    v___x_7352_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_7306_, v_b_7307_, v_bkt_7331_);
                    v___x_7353_ = lean_array_uset(v_buckets_x27_7351_, v___x_7330_, v___x_7352_);
                    if v_isShared_7312_ == 0 {
                        leanh::lean_ctor_set(v___x_7311_, 1, v___x_7353_);
                        v___x_7355_ = v___x_7311_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7356_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7356_, 0, v_size_7308_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7356_, 1, v___x_7353_);
                        v___x_7355_ = v_reuseFailAlloc_7356_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_7345_;
            }
            4 => {
                return v___x_7348_;
            }
            5 => {
                return v___x_7355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(
    mut v_a_7361_: *mut leanh::LeanObject,
    mut v_x_7362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_7364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7372_: u8 = 0;
    let mut v___x_7374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7375_: u8 = 0;
    let mut v___x_7376_: u8 = 0;
    let mut v___x_7378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7362_) == 0 {
                    v___x_7363_ = leanh::lean_box(0);
                    return v___x_7363_;
                } else {
                    v_key_7364_ = leanh::lean_ctor_get(v_x_7362_, 0);
                    v_value_7365_ = leanh::lean_ctor_get(v_x_7362_, 1);
                    v_tail_7366_ = leanh::lean_ctor_get(v_x_7362_, 2);
                    v_fst_7367_ = leanh::lean_ctor_get(v_key_7364_, 0);
                    v_snd_7368_ = leanh::lean_ctor_get(v_key_7364_, 1);
                    v_fst_7369_ = leanh::lean_ctor_get(v_a_7361_, 0);
                    v_snd_7370_ = leanh::lean_ctor_get(v_a_7361_, 1);
                    v___x_7375_ = (leanh::lean_unbox(v_fst_7367_) as u8);
                    if v___x_7375_ == 0 {
                        v___x_7376_ = (leanh::lean_unbox(v_fst_7369_) as u8);
                        if v___x_7376_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v_x_7362_ = v_tail_7366_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_7378_ = (leanh::lean_unbox(v_fst_7369_) as u8);
                        if v___x_7378_ == 0 {
                            v_x_7362_ = v_tail_7366_;
                            state = 0;
                            continue;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7372_ = l_Lean_ExprStructEq_beq(v_snd_7368_, v_snd_7370_);
                if v___x_7372_ == 0 {
                    v_x_7362_ = v_tail_7366_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_inc(v_value_7365_);
                    v___x_7374_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7374_, 0, v_value_7365_);
                    return v___x_7374_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg___boxed(
    mut v_a_7380_: *mut leanh::LeanObject,
    mut v_x_7381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7382_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_7380_, v_x_7381_);
    leanh::lean_dec(v_x_7381_);
    leanh::lean_dec_ref(v_a_7380_);
    return v_res_7382_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(
    mut v_m_7383_: *mut leanh::LeanObject,
    mut v_a_7384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_7385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7390_: u64 = 0;
    let mut v___x_7391_: u64 = 0;
    let mut v___x_7392_: u64 = 0;
    let mut v___x_7393_: u64 = 0;
    let mut v___x_7394_: u64 = 0;
    let mut v_fold_7395_: u64 = 0;
    let mut v___x_7396_: u64 = 0;
    let mut v___x_7397_: u64 = 0;
    let mut v___x_7398_: u64 = 0;
    let mut v___x_7399_: usize = 0;
    let mut v___x_7400_: usize = 0;
    let mut v___x_7401_: usize = 0;
    let mut v___x_7402_: usize = 0;
    let mut v___x_7403_: usize = 0;
    let mut v___x_7404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7406_: u8 = 0;
    let mut v___x_7407_: u64 = 0;
    let mut v___x_7408_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_7385_ = leanh::lean_ctor_get(v_m_7383_, 1);
                v_fst_7386_ = leanh::lean_ctor_get(v_a_7384_, 0);
                v_snd_7387_ = leanh::lean_ctor_get(v_a_7384_, 1);
                v___x_7388_ = lean_array_get_size(v_buckets_7385_);
                v___x_7406_ = (leanh::lean_unbox(v_fst_7386_) as u8);
                if v___x_7406_ == 0 {
                    v___x_7407_ = 13u64;
                    v___y_7390_ = v___x_7407_;
                    state = 1;
                    continue;
                } else {
                    v___x_7408_ = 11u64;
                    v___y_7390_ = v___x_7408_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7391_ = l_Lean_ExprStructEq_hash(v_snd_7387_);
                v___x_7392_ = lean_uint64_mix_hash(v___y_7390_, v___x_7391_);
                v___x_7393_ = 32u64;
                v___x_7394_ = lean_uint64_shift_right(v___x_7392_, v___x_7393_);
                v_fold_7395_ = lean_uint64_xor(v___x_7392_, v___x_7394_);
                v___x_7396_ = 16u64;
                v___x_7397_ = lean_uint64_shift_right(v_fold_7395_, v___x_7396_);
                v___x_7398_ = lean_uint64_xor(v_fold_7395_, v___x_7397_);
                v___x_7399_ = lean_uint64_to_usize(v___x_7398_);
                v___x_7400_ = lean_usize_of_nat(v___x_7388_);
                v___x_7401_ = 1usize;
                v___x_7402_ = lean_usize_sub(v___x_7400_, v___x_7401_);
                v___x_7403_ = lean_usize_land(v___x_7399_, v___x_7402_);
                v___x_7404_ = lean_array_uget_borrowed(v_buckets_7385_, v___x_7403_);
                v___x_7405_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_7384_, v___x_7404_);
                return v___x_7405_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg___boxed(
    mut v_m_7409_: *mut leanh::LeanObject,
    mut v_a_7410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7411_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_7409_, v_a_7410_);
    leanh::lean_dec_ref(v_a_7410_);
    leanh::lean_dec_ref(v_m_7409_);
    return v_res_7411_;
}
pub unsafe fn _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_7412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_7413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7412_ = leanh::lean_box(0);
    v_dummy_7413_ = l_Lean_Expr_sort___override(v___x_7412_);
    return v_dummy_7413_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(
    mut v_upperBound_7414_: *mut leanh::LeanObject,
    mut v_fst_7415_: *mut leanh::LeanObject,
    mut v_fvars_7416_: *mut leanh::LeanObject,
    mut v_a_7417_: *mut leanh::LeanObject,
    mut v_b_7418_: *mut leanh::LeanObject,
    mut v___y_7419_: *mut leanh::LeanObject,
    mut v___y_7420_: *mut leanh::LeanObject,
    mut v___y_7421_: *mut leanh::LeanObject,
    mut v___y_7422_: *mut leanh::LeanObject,
    mut v___y_7423_: *mut leanh::LeanObject,
    mut v___y_7424_: *mut leanh::LeanObject,
    mut v___y_7425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_7428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7432_: u8 = 0;
    let mut v___x_7433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_7436_: u8 = 0;
    let mut v___x_7437_: u8 = 0;
    let mut v___x_7438_: u8 = 0;
    let mut v___x_7439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7447_: u8 = 0;
    let mut v___x_7449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7451_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7432_ = lean_nat_dec_lt(v_a_7417_, v_upperBound_7414_);
                if v___x_7432_ == 0 {
                    leanh::lean_dec(v_a_7417_);
                    leanh::lean_dec(v_fvars_7416_);
                    v___x_7433_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7433_, 0, v_b_7418_);
                    return v___x_7433_;
                } else {
                    v___x_7434_ = l_Lean_Meta_instInhabitedExprParamInfo_default;
                    v___x_7435_ = lean_array_get_borrowed(v___x_7434_, v_fst_7415_, v_a_7417_);
                    v_binderInfo_7436_ = leanh::lean_ctor_get_uint8(
                        v___x_7435_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___x_7437_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_7436_);
                    if v___x_7437_ == 0 {
                        v_a_7428_ = v_b_7418_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7438_ = 0;
                        v___x_7439_ = l_Lean_instInhabitedExpr;
                        v___x_7440_ = lean_array_get_borrowed(v___x_7439_, v_b_7418_, v_a_7417_);
                        leanh::lean_inc(v___x_7440_);
                        leanh::lean_inc(v_fvars_7416_);
                        v___x_7441_ = l_Lean_Meta_ExtractLets_extractCore(
                            v_fvars_7416_,
                            v___x_7440_,
                            v___x_7438_,
                            v___y_7419_,
                            v___y_7420_,
                            v___y_7421_,
                            v___y_7422_,
                            v___y_7423_,
                            v___y_7424_,
                            v___y_7425_,
                        );
                        if leanh::lean_obj_tag(v___x_7441_) == 0 {
                            v_a_7442_ = leanh::lean_ctor_get(v___x_7441_, 0);
                            leanh::lean_inc(v_a_7442_);
                            leanh::lean_dec_ref_known(v___x_7441_, 1);
                            v___x_7443_ = lean_array_set(v_b_7418_, v_a_7417_, v_a_7442_);
                            v_a_7428_ = v___x_7443_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_b_7418_);
                            leanh::lean_dec(v_a_7417_);
                            leanh::lean_dec(v_fvars_7416_);
                            v_a_7444_ = leanh::lean_ctor_get(v___x_7441_, 0);
                            v_isSharedCheck_7451_ =
                                (!leanh::lean_is_exclusive(v___x_7441_)) as u8;
                            if v_isSharedCheck_7451_ == 0 {
                                v___x_7446_ = v___x_7441_;
                                v_isShared_7447_ = v_isSharedCheck_7451_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7444_);
                                leanh::lean_dec(v___x_7441_);
                                v___x_7446_ = leanh::lean_box(0);
                                v_isShared_7447_ = v_isSharedCheck_7451_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_7429_ = leanh::lean_unsigned_to_nat(1);
                v___x_7430_ = lean_nat_add(v_a_7417_, v___x_7429_);
                leanh::lean_dec(v_a_7417_);
                v_a_7417_ = v___x_7430_;
                v_b_7418_ = v_a_7428_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_7447_ == 0 {
                    v___x_7449_ = v___x_7446_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7450_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7450_, 0, v_a_7444_);
                    v___x_7449_ = v_reuseFailAlloc_7450_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7449_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(
    mut v_fvars_7452_: *mut leanh::LeanObject,
    mut v_sz_7453_: usize,
    mut v_i_7454_: usize,
    mut v_bs_7455_: *mut leanh::LeanObject,
    mut v___y_7456_: *mut leanh::LeanObject,
    mut v___y_7457_: *mut leanh::LeanObject,
    mut v___y_7458_: *mut leanh::LeanObject,
    mut v___y_7459_: *mut leanh::LeanObject,
    mut v___y_7460_: *mut leanh::LeanObject,
    mut v___y_7461_: *mut leanh::LeanObject,
    mut v___y_7462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7464_: u8 = 0;
    let mut v___x_7465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7466_: u8 = 0;
    let mut v_v_7467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7472_: usize = 0;
    let mut v___x_7473_: usize = 0;
    let mut v___x_7474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7479_: u8 = 0;
    let mut v___x_7481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7483_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7464_ = lean_usize_dec_lt(v_i_7454_, v_sz_7453_);
                if v___x_7464_ == 0 {
                    leanh::lean_dec(v_fvars_7452_);
                    v___x_7465_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7465_, 0, v_bs_7455_);
                    return v___x_7465_;
                } else {
                    v___x_7466_ = 0;
                    v_v_7467_ = lean_array_uget_borrowed(v_bs_7455_, v_i_7454_);
                    leanh::lean_inc(v_v_7467_);
                    leanh::lean_inc(v_fvars_7452_);
                    v___x_7468_ = l_Lean_Meta_ExtractLets_extractCore(
                        v_fvars_7452_,
                        v_v_7467_,
                        v___x_7466_,
                        v___y_7456_,
                        v___y_7457_,
                        v___y_7458_,
                        v___y_7459_,
                        v___y_7460_,
                        v___y_7461_,
                        v___y_7462_,
                    );
                    if leanh::lean_obj_tag(v___x_7468_) == 0 {
                        v_a_7469_ = leanh::lean_ctor_get(v___x_7468_, 0);
                        leanh::lean_inc(v_a_7469_);
                        leanh::lean_dec_ref_known(v___x_7468_, 1);
                        v___x_7470_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_7471_ = lean_array_uset(v_bs_7455_, v_i_7454_, v___x_7470_);
                        v___x_7472_ = 1usize;
                        v___x_7473_ = lean_usize_add(v_i_7454_, v___x_7472_);
                        v___x_7474_ = lean_array_uset(v_bs_x27_7471_, v_i_7454_, v_a_7469_);
                        v_i_7454_ = v___x_7473_;
                        v_bs_7455_ = v___x_7474_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_7455_);
                        leanh::lean_dec(v_fvars_7452_);
                        v_a_7476_ = leanh::lean_ctor_get(v___x_7468_, 0);
                        v_isSharedCheck_7483_ =
                            (!leanh::lean_is_exclusive(v___x_7468_)) as u8;
                        if v_isSharedCheck_7483_ == 0 {
                            v___x_7478_ = v___x_7468_;
                            v_isShared_7479_ = v_isSharedCheck_7483_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7476_);
                            leanh::lean_dec(v___x_7468_);
                            v___x_7478_ = leanh::lean_box(0);
                            v_isShared_7479_ = v_isSharedCheck_7483_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_7479_ == 0 {
                    v___x_7481_ = v___x_7478_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7482_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7482_, 0, v_a_7476_);
                    v___x_7481_ = v_reuseFailAlloc_7482_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7481_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(
    mut v_fvars_7484_: *mut leanh::LeanObject,
    mut v_f_7485_: *mut leanh::LeanObject,
    mut v_args_7486_: *mut leanh::LeanObject,
    mut v_a_7487_: *mut leanh::LeanObject,
    mut v_a_7488_: *mut leanh::LeanObject,
    mut v_a_7489_: *mut leanh::LeanObject,
    mut v_a_7490_: *mut leanh::LeanObject,
    mut v_a_7491_: *mut leanh::LeanObject,
    mut v_a_7492_: *mut leanh::LeanObject,
    mut v_a_7493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7495_: u8 = 0;
    let mut v___x_7496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_implicits_7497_: u8 = 0;
    let mut v_a_7498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7510_: u8 = 0;
    let mut v___x_7511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7515_: u8 = 0;
    let mut v_a_7516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7519_: u8 = 0;
    let mut v___x_7521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7523_: u8 = 0;
    let mut v_a_7524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7527_: u8 = 0;
    let mut v___x_7529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7531_: u8 = 0;
    let mut v_a_7532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7533_: usize = 0;
    let mut v___x_7534_: usize = 0;
    let mut v___x_7535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7539_: u8 = 0;
    let mut v___x_7540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7544_: u8 = 0;
    let mut v_a_7545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7548_: u8 = 0;
    let mut v___x_7550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7552_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7495_ = 0;
                leanh::lean_inc_ref(v_f_7485_);
                leanh::lean_inc(v_fvars_7484_);
                v___x_7496_ = l_Lean_Meta_ExtractLets_extractCore(
                    v_fvars_7484_,
                    v_f_7485_,
                    v___x_7495_,
                    v_a_7487_,
                    v_a_7488_,
                    v_a_7489_,
                    v_a_7490_,
                    v_a_7491_,
                    v_a_7492_,
                    v_a_7493_,
                );
                if leanh::lean_obj_tag(v___x_7496_) == 0 {
                    v_implicits_7497_ = leanh::lean_ctor_get_uint8(v_a_7487_, 2 as u32);
                    if v_implicits_7497_ == 0 {
                        v_a_7498_ = leanh::lean_ctor_get(v___x_7496_, 0);
                        leanh::lean_inc(v_a_7498_);
                        leanh::lean_dec_ref_known(v___x_7496_, 1);
                        leanh::lean_inc(v_a_7493_);
                        leanh::lean_inc_ref(v_a_7492_);
                        leanh::lean_inc(v_a_7491_);
                        leanh::lean_inc_ref(v_a_7490_);
                        v___x_7499_ =
                            lean_infer_type(v_f_7485_, v_a_7490_, v_a_7491_, v_a_7492_, v_a_7493_);
                        if leanh::lean_obj_tag(v___x_7499_) == 0 {
                            v_a_7500_ = leanh::lean_ctor_get(v___x_7499_, 0);
                            leanh::lean_inc(v_a_7500_);
                            leanh::lean_dec_ref_known(v___x_7499_, 1);
                            v___x_7501_ = l_Lean_Meta_instantiateForallWithParamInfos(
                                v_a_7500_,
                                v_args_7486_,
                                v___x_7495_,
                                v_a_7490_,
                                v_a_7491_,
                                v_a_7492_,
                                v_a_7493_,
                            );
                            if leanh::lean_obj_tag(v___x_7501_) == 0 {
                                v_a_7502_ = leanh::lean_ctor_get(v___x_7501_, 0);
                                leanh::lean_inc(v_a_7502_);
                                leanh::lean_dec_ref_known(v___x_7501_, 1);
                                v_fst_7503_ = leanh::lean_ctor_get(v_a_7502_, 0);
                                leanh::lean_inc(v_fst_7503_);
                                leanh::lean_dec(v_a_7502_);
                                v___x_7504_ = lean_array_get_size(v_args_7486_);
                                v___x_7505_ = leanh::lean_unsigned_to_nat(0);
                                v___x_7506_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v___x_7504_, v_fst_7503_, v_fvars_7484_, v___x_7505_, v_args_7486_, v_a_7487_, v_a_7488_, v_a_7489_, v_a_7490_, v_a_7491_, v_a_7492_, v_a_7493_);
                                leanh::lean_dec(v_fst_7503_);
                                if leanh::lean_obj_tag(v___x_7506_) == 0 {
                                    v_a_7507_ = leanh::lean_ctor_get(v___x_7506_, 0);
                                    v_isSharedCheck_7515_ =
                                        (!leanh::lean_is_exclusive(v___x_7506_)) as u8;
                                    if v_isSharedCheck_7515_ == 0 {
                                        v___x_7509_ = v___x_7506_;
                                        v_isShared_7510_ = v_isSharedCheck_7515_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_7507_);
                                        leanh::lean_dec(v___x_7506_);
                                        v___x_7509_ = leanh::lean_box(0);
                                        v_isShared_7510_ = v_isSharedCheck_7515_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_7498_);
                                    v_a_7516_ = leanh::lean_ctor_get(v___x_7506_, 0);
                                    v_isSharedCheck_7523_ =
                                        (!leanh::lean_is_exclusive(v___x_7506_)) as u8;
                                    if v_isSharedCheck_7523_ == 0 {
                                        v___x_7518_ = v___x_7506_;
                                        v_isShared_7519_ = v_isSharedCheck_7523_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_7516_);
                                        leanh::lean_dec(v___x_7506_);
                                        v___x_7518_ = leanh::lean_box(0);
                                        v_isShared_7519_ = v_isSharedCheck_7523_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_7498_);
                                leanh::lean_dec_ref(v_args_7486_);
                                leanh::lean_dec(v_fvars_7484_);
                                v_a_7524_ = leanh::lean_ctor_get(v___x_7501_, 0);
                                v_isSharedCheck_7531_ =
                                    (!leanh::lean_is_exclusive(v___x_7501_)) as u8;
                                if v_isSharedCheck_7531_ == 0 {
                                    v___x_7526_ = v___x_7501_;
                                    v_isShared_7527_ = v_isSharedCheck_7531_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_7524_);
                                    leanh::lean_dec(v___x_7501_);
                                    v___x_7526_ = leanh::lean_box(0);
                                    v_isShared_7527_ = v_isSharedCheck_7531_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_7498_);
                            leanh::lean_dec_ref(v_args_7486_);
                            leanh::lean_dec(v_fvars_7484_);
                            return v___x_7499_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_f_7485_);
                        v_a_7532_ = leanh::lean_ctor_get(v___x_7496_, 0);
                        leanh::lean_inc(v_a_7532_);
                        leanh::lean_dec_ref_known(v___x_7496_, 1);
                        v_sz_7533_ = lean_array_size(v_args_7486_);
                        v___x_7534_ = 0usize;
                        v___x_7535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_7484_, v_sz_7533_, v___x_7534_, v_args_7486_, v_a_7487_, v_a_7488_, v_a_7489_, v_a_7490_, v_a_7491_, v_a_7492_, v_a_7493_);
                        if leanh::lean_obj_tag(v___x_7535_) == 0 {
                            v_a_7536_ = leanh::lean_ctor_get(v___x_7535_, 0);
                            v_isSharedCheck_7544_ =
                                (!leanh::lean_is_exclusive(v___x_7535_)) as u8;
                            if v_isSharedCheck_7544_ == 0 {
                                v___x_7538_ = v___x_7535_;
                                v_isShared_7539_ = v_isSharedCheck_7544_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7536_);
                                leanh::lean_dec(v___x_7535_);
                                v___x_7538_ = leanh::lean_box(0);
                                v_isShared_7539_ = v_isSharedCheck_7544_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_7532_);
                            v_a_7545_ = leanh::lean_ctor_get(v___x_7535_, 0);
                            v_isSharedCheck_7552_ =
                                (!leanh::lean_is_exclusive(v___x_7535_)) as u8;
                            if v_isSharedCheck_7552_ == 0 {
                                v___x_7547_ = v___x_7535_;
                                v_isShared_7548_ = v_isSharedCheck_7552_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7545_);
                                leanh::lean_dec(v___x_7535_);
                                v___x_7547_ = leanh::lean_box(0);
                                v_isShared_7548_ = v_isSharedCheck_7552_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_args_7486_);
                    leanh::lean_dec_ref(v_f_7485_);
                    leanh::lean_dec(v_fvars_7484_);
                    return v___x_7496_;
                }
            }
            1 => {
                v___x_7511_ = l_Lean_mkAppN(v_a_7498_, v_a_7507_);
                leanh::lean_dec(v_a_7507_);
                if v_isShared_7510_ == 0 {
                    leanh::lean_ctor_set(v___x_7509_, 0, v___x_7511_);
                    v___x_7513_ = v___x_7509_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7514_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7514_, 0, v___x_7511_);
                    v___x_7513_ = v_reuseFailAlloc_7514_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7513_;
            }
            3 => {
                if v_isShared_7519_ == 0 {
                    v___x_7521_ = v___x_7518_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7522_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7522_, 0, v_a_7516_);
                    v___x_7521_ = v_reuseFailAlloc_7522_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7521_;
            }
            5 => {
                if v_isShared_7527_ == 0 {
                    v___x_7529_ = v___x_7526_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7530_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7530_, 0, v_a_7524_);
                    v___x_7529_ = v_reuseFailAlloc_7530_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7529_;
            }
            7 => {
                v___x_7540_ = l_Lean_mkAppN(v_a_7532_, v_a_7536_);
                leanh::lean_dec(v_a_7536_);
                if v_isShared_7539_ == 0 {
                    leanh::lean_ctor_set(v___x_7538_, 0, v___x_7540_);
                    v___x_7542_ = v___x_7538_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7543_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7543_, 0, v___x_7540_);
                    v___x_7542_ = v_reuseFailAlloc_7543_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7542_;
            }
            9 => {
                if v_isShared_7548_ == 0 {
                    v___x_7550_ = v___x_7547_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7551_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7551_, 0, v_a_7545_);
                    v___x_7550_ = v_reuseFailAlloc_7551_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7550_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed(
    mut v_fvars_7553_: *mut leanh::LeanObject,
    mut v_f_7554_: *mut leanh::LeanObject,
    mut v_args_7555_: *mut leanh::LeanObject,
    mut v_a_7556_: *mut leanh::LeanObject,
    mut v_a_7557_: *mut leanh::LeanObject,
    mut v_a_7558_: *mut leanh::LeanObject,
    mut v_a_7559_: *mut leanh::LeanObject,
    mut v_a_7560_: *mut leanh::LeanObject,
    mut v_a_7561_: *mut leanh::LeanObject,
    mut v_a_7562_: *mut leanh::LeanObject,
    mut v_a_7563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7564_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp(
        v_fvars_7553_,
        v_f_7554_,
        v_args_7555_,
        v_a_7556_,
        v_a_7557_,
        v_a_7558_,
        v_a_7559_,
        v_a_7560_,
        v_a_7561_,
        v_a_7562_,
    );
    leanh::lean_dec(v_a_7562_);
    leanh::lean_dec_ref(v_a_7561_);
    leanh::lean_dec(v_a_7560_);
    leanh::lean_dec_ref(v_a_7559_);
    leanh::lean_dec(v_a_7558_);
    leanh::lean_dec(v_a_7557_);
    leanh::lean_dec_ref(v_a_7556_);
    return v_res_7564_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(
    mut v_fvars_7565_: *mut leanh::LeanObject,
    mut v_b_7566_: *mut leanh::LeanObject,
    mut v___x_7567_: u8,
    mut v_mk_7568_: *mut leanh::LeanObject,
    mut v_a_7569_: *mut leanh::LeanObject,
    mut v_x_7570_: *mut leanh::LeanObject,
    mut v___y_7571_: *mut leanh::LeanObject,
    mut v___y_7572_: *mut leanh::LeanObject,
    mut v___y_7573_: *mut leanh::LeanObject,
    mut v___y_7574_: *mut leanh::LeanObject,
    mut v___y_7575_: *mut leanh::LeanObject,
    mut v___y_7576_: *mut leanh::LeanObject,
    mut v___y_7577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lift_7582_: u8 = 0;
    let mut v_a_7583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7586_: u8 = 0;
    let mut v___x_7587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7595_: u8 = 0;
    let mut v_a_7596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7602_: u8 = 0;
    let mut v___x_7603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7612_: u8 = 0;
    let mut v_a_7613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7616_: u8 = 0;
    let mut v___x_7618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_x_7570_);
                v___x_7579_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7579_, 0, v_x_7570_);
                leanh::lean_ctor_set(v___x_7579_, 1, v_fvars_7565_);
                v___x_7580_ = lean_expr_instantiate1(v_b_7566_, v_x_7570_);
                v___x_7581_ = l_Lean_Meta_ExtractLets_extractCore(
                    v___x_7579_,
                    v___x_7580_,
                    v___x_7567_,
                    v___y_7571_,
                    v___y_7572_,
                    v___y_7573_,
                    v___y_7574_,
                    v___y_7575_,
                    v___y_7576_,
                    v___y_7577_,
                );
                if leanh::lean_obj_tag(v___x_7581_) == 0 {
                    v_lift_7582_ = leanh::lean_ctor_get_uint8(v___y_7571_, 10 as u32);
                    if v_lift_7582_ == 0 {
                        v_a_7583_ = leanh::lean_ctor_get(v___x_7581_, 0);
                        v_isSharedCheck_7595_ =
                            (!leanh::lean_is_exclusive(v___x_7581_)) as u8;
                        if v_isSharedCheck_7595_ == 0 {
                            v___x_7585_ = v___x_7581_;
                            v_isShared_7586_ = v_isSharedCheck_7595_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7583_);
                            leanh::lean_dec(v___x_7581_);
                            v___x_7585_ = leanh::lean_box(0);
                            v_isShared_7586_ = v_isSharedCheck_7595_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_7596_ = leanh::lean_ctor_get(v___x_7581_, 0);
                        leanh::lean_inc(v_a_7596_);
                        leanh::lean_dec_ref_known(v___x_7581_, 1);
                        v___x_7597_ = l_Lean_Expr_fvarId_x21(v_x_7570_);
                        v___x_7598_ = l_Lean_Meta_ExtractLets_flushDecls(
                            v___x_7597_,
                            v___y_7571_,
                            v___y_7572_,
                            v___y_7573_,
                            v___y_7574_,
                            v___y_7575_,
                            v___y_7576_,
                            v___y_7577_,
                        );
                        if leanh::lean_obj_tag(v___x_7598_) == 0 {
                            v_a_7599_ = leanh::lean_ctor_get(v___x_7598_, 0);
                            v_isSharedCheck_7612_ =
                                (!leanh::lean_is_exclusive(v___x_7598_)) as u8;
                            if v_isSharedCheck_7612_ == 0 {
                                v___x_7601_ = v___x_7598_;
                                v_isShared_7602_ = v_isSharedCheck_7612_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7599_);
                                leanh::lean_dec(v___x_7598_);
                                v___x_7601_ = leanh::lean_box(0);
                                v_isShared_7602_ = v_isSharedCheck_7612_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_7596_);
                            leanh::lean_dec_ref(v_x_7570_);
                            leanh::lean_dec_ref(v_a_7569_);
                            leanh::lean_dec_ref(v_mk_7568_);
                            v_a_7613_ = leanh::lean_ctor_get(v___x_7598_, 0);
                            v_isSharedCheck_7620_ =
                                (!leanh::lean_is_exclusive(v___x_7598_)) as u8;
                            if v_isSharedCheck_7620_ == 0 {
                                v___x_7615_ = v___x_7598_;
                                v_isShared_7616_ = v_isSharedCheck_7620_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7613_);
                                leanh::lean_dec(v___x_7598_);
                                v___x_7615_ = leanh::lean_box(0);
                                v_isShared_7616_ = v_isSharedCheck_7620_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_x_7570_);
                    leanh::lean_dec_ref(v_a_7569_);
                    leanh::lean_dec_ref(v_mk_7568_);
                    return v___x_7581_;
                }
            }
            1 => {
                v___x_7587_ = leanh::lean_unsigned_to_nat(1);
                v___x_7588_ = lean_mk_empty_array_with_capacity(v___x_7587_);
                v___x_7589_ = lean_array_push(v___x_7588_, v_x_7570_);
                v___x_7590_ = lean_expr_abstract(v_a_7583_, v___x_7589_);
                leanh::lean_dec_ref(v___x_7589_);
                leanh::lean_dec(v_a_7583_);
                v___x_7591_ = leanh::lean_apply_2(v_mk_7568_, v_a_7569_, v___x_7590_);
                if v_isShared_7586_ == 0 {
                    leanh::lean_ctor_set(v___x_7585_, 0, v___x_7591_);
                    v___x_7593_ = v___x_7585_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7594_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7594_, 0, v___x_7591_);
                    v___x_7593_ = v_reuseFailAlloc_7594_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7593_;
            }
            3 => {
                v___x_7603_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_a_7599_, v_a_7596_);
                leanh::lean_dec(v_a_7599_);
                v___x_7604_ = leanh::lean_unsigned_to_nat(1);
                v___x_7605_ = lean_mk_empty_array_with_capacity(v___x_7604_);
                v___x_7606_ = lean_array_push(v___x_7605_, v_x_7570_);
                v___x_7607_ = lean_expr_abstract(v___x_7603_, v___x_7606_);
                leanh::lean_dec_ref(v___x_7606_);
                leanh::lean_dec_ref(v___x_7603_);
                v___x_7608_ = leanh::lean_apply_2(v_mk_7568_, v_a_7569_, v___x_7607_);
                if v_isShared_7602_ == 0 {
                    leanh::lean_ctor_set(v___x_7601_, 0, v___x_7608_);
                    v___x_7610_ = v___x_7601_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7611_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7611_, 0, v___x_7608_);
                    v___x_7610_ = v_reuseFailAlloc_7611_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7610_;
            }
            5 => {
                if v_isShared_7616_ == 0 {
                    v___x_7618_ = v___x_7615_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7619_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7619_, 0, v_a_7613_);
                    v___x_7618_ = v_reuseFailAlloc_7619_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7618_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed(
    mut v_fvars_7621_: *mut leanh::LeanObject,
    mut v_b_7622_: *mut leanh::LeanObject,
    mut v___x_7623_: *mut leanh::LeanObject,
    mut v_mk_7624_: *mut leanh::LeanObject,
    mut v_a_7625_: *mut leanh::LeanObject,
    mut v_x_7626_: *mut leanh::LeanObject,
    mut v___y_7627_: *mut leanh::LeanObject,
    mut v___y_7628_: *mut leanh::LeanObject,
    mut v___y_7629_: *mut leanh::LeanObject,
    mut v___y_7630_: *mut leanh::LeanObject,
    mut v___y_7631_: *mut leanh::LeanObject,
    mut v___y_7632_: *mut leanh::LeanObject,
    mut v___y_7633_: *mut leanh::LeanObject,
    mut v___y_7634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_51510__boxed_7635_: u8 = 0;
    let mut v_res_7636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_51510__boxed_7635_ = (leanh::lean_unbox(v___x_7623_) as u8);
    v_res_7636_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0(v_fvars_7621_, v_b_7622_, v___x_51510__boxed_7635_, v_mk_7624_, v_a_7625_, v_x_7626_, v___y_7627_, v___y_7628_, v___y_7629_, v___y_7630_, v___y_7631_, v___y_7632_, v___y_7633_);
    leanh::lean_dec(v___y_7633_);
    leanh::lean_dec_ref(v___y_7632_);
    leanh::lean_dec(v___y_7631_);
    leanh::lean_dec_ref(v___y_7630_);
    leanh::lean_dec(v___y_7629_);
    leanh::lean_dec(v___y_7628_);
    leanh::lean_dec_ref(v___y_7627_);
    leanh::lean_dec_ref(v_b_7622_);
    return v_res_7636_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(
    mut v_fvars_7637_: *mut leanh::LeanObject,
    mut v_n_7638_: *mut leanh::LeanObject,
    mut v_t_7639_: *mut leanh::LeanObject,
    mut v_b_7640_: *mut leanh::LeanObject,
    mut v_i_7641_: u8,
    mut v_mk_7642_: *mut leanh::LeanObject,
    mut v_a_7643_: *mut leanh::LeanObject,
    mut v_a_7644_: *mut leanh::LeanObject,
    mut v_a_7645_: *mut leanh::LeanObject,
    mut v_a_7646_: *mut leanh::LeanObject,
    mut v_a_7647_: *mut leanh::LeanObject,
    mut v_a_7648_: *mut leanh::LeanObject,
    mut v_a_7649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7651_: u8 = 0;
    let mut v___x_7652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_underBinder_7653_: u8 = 0;
    let mut v_a_7654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7657_: u8 = 0;
    let mut v___x_7658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7662_: u8 = 0;
    let mut v_a_7663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7666_: u8 = 0;
    let mut v___x_7667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7651_ = 0;
                leanh::lean_inc(v_fvars_7637_);
                v___x_7652_ = l_Lean_Meta_ExtractLets_extractCore(
                    v_fvars_7637_,
                    v_t_7639_,
                    v___x_7651_,
                    v_a_7643_,
                    v_a_7644_,
                    v_a_7645_,
                    v_a_7646_,
                    v_a_7647_,
                    v_a_7648_,
                    v_a_7649_,
                );
                if leanh::lean_obj_tag(v___x_7652_) == 0 {
                    v_underBinder_7653_ = leanh::lean_ctor_get_uint8(v_a_7643_, 4 as u32);
                    if v_underBinder_7653_ == 0 {
                        leanh::lean_dec(v_n_7638_);
                        leanh::lean_dec(v_fvars_7637_);
                        v_a_7654_ = leanh::lean_ctor_get(v___x_7652_, 0);
                        v_isSharedCheck_7662_ =
                            (!leanh::lean_is_exclusive(v___x_7652_)) as u8;
                        if v_isSharedCheck_7662_ == 0 {
                            v___x_7656_ = v___x_7652_;
                            v_isShared_7657_ = v_isSharedCheck_7662_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7654_);
                            leanh::lean_dec(v___x_7652_);
                            v___x_7656_ = leanh::lean_box(0);
                            v_isShared_7657_ = v_isSharedCheck_7662_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_7663_ = leanh::lean_ctor_get(v___x_7652_, 0);
                        leanh::lean_inc_n(v_a_7663_, 2);
                        leanh::lean_dec_ref_known(v___x_7652_, 1);
                        v___x_7664_ = leanh::lean_box((v___x_7651_) as usize);
                        v___f_7665_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___lam__0___boxed as *mut core::ffi::c_void, 14, 5);
                        leanh::lean_closure_set(v___f_7665_, 0, v_fvars_7637_);
                        leanh::lean_closure_set(v___f_7665_, 1, v_b_7640_);
                        leanh::lean_closure_set(v___f_7665_, 2, v___x_7664_);
                        leanh::lean_closure_set(v___f_7665_, 3, v_mk_7642_);
                        leanh::lean_closure_set(v___f_7665_, 4, v_a_7663_);
                        v___x_7666_ = 0;
                        v___x_7667_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder_spec__0___redArg(v_n_7638_, v_i_7641_, v_a_7663_, v___f_7665_, v___x_7666_, v_a_7643_, v_a_7644_, v_a_7645_, v_a_7646_, v_a_7647_, v_a_7648_, v_a_7649_);
                        return v___x_7667_;
                    }
                } else {
                    leanh::lean_dec_ref(v_mk_7642_);
                    leanh::lean_dec_ref(v_b_7640_);
                    leanh::lean_dec(v_n_7638_);
                    leanh::lean_dec(v_fvars_7637_);
                    return v___x_7652_;
                }
            }
            1 => {
                v___x_7658_ = leanh::lean_apply_2(v_mk_7642_, v_a_7654_, v_b_7640_);
                if v_isShared_7657_ == 0 {
                    leanh::lean_ctor_set(v___x_7656_, 0, v___x_7658_);
                    v___x_7660_ = v___x_7656_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7661_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7661_, 0, v___x_7658_);
                    v___x_7660_ = v_reuseFailAlloc_7661_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed(
    mut v_fvars_7668_: *mut leanh::LeanObject,
    mut v_n_7669_: *mut leanh::LeanObject,
    mut v_t_7670_: *mut leanh::LeanObject,
    mut v_b_7671_: *mut leanh::LeanObject,
    mut v_i_7672_: *mut leanh::LeanObject,
    mut v_mk_7673_: *mut leanh::LeanObject,
    mut v_a_7674_: *mut leanh::LeanObject,
    mut v_a_7675_: *mut leanh::LeanObject,
    mut v_a_7676_: *mut leanh::LeanObject,
    mut v_a_7677_: *mut leanh::LeanObject,
    mut v_a_7678_: *mut leanh::LeanObject,
    mut v_a_7679_: *mut leanh::LeanObject,
    mut v_a_7680_: *mut leanh::LeanObject,
    mut v_a_7681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_7682_: u8 = 0;
    let mut v_res_7683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7682_ = (leanh::lean_unbox(v_i_7672_) as u8);
    v_res_7683_ =
        l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder(
            v_fvars_7668_,
            v_n_7669_,
            v_t_7670_,
            v_b_7671_,
            v_i_boxed_7682_,
            v_mk_7673_,
            v_a_7674_,
            v_a_7675_,
            v_a_7676_,
            v_a_7677_,
            v_a_7678_,
            v_a_7679_,
            v_a_7680_,
        );
    leanh::lean_dec(v_a_7680_);
    leanh::lean_dec_ref(v_a_7679_);
    leanh::lean_dec(v_a_7678_);
    leanh::lean_dec_ref(v_a_7677_);
    leanh::lean_dec(v_a_7676_);
    leanh::lean_dec(v_a_7675_);
    leanh::lean_dec_ref(v_a_7674_);
    return v_res_7683_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_extractCore___boxed(
    mut v_fvars_7684_: *mut leanh::LeanObject,
    mut v_e_7685_: *mut leanh::LeanObject,
    mut v_topLevel_7686_: *mut leanh::LeanObject,
    mut v_a_7687_: *mut leanh::LeanObject,
    mut v_a_7688_: *mut leanh::LeanObject,
    mut v_a_7689_: *mut leanh::LeanObject,
    mut v_a_7690_: *mut leanh::LeanObject,
    mut v_a_7691_: *mut leanh::LeanObject,
    mut v_a_7692_: *mut leanh::LeanObject,
    mut v_a_7693_: *mut leanh::LeanObject,
    mut v_a_7694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_topLevel_boxed_7695_: u8 = 0;
    let mut v_res_7696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_topLevel_boxed_7695_ = (leanh::lean_unbox(v_topLevel_7686_) as u8);
    v_res_7696_ = l_Lean_Meta_ExtractLets_extractCore(
        v_fvars_7684_,
        v_e_7685_,
        v_topLevel_boxed_7695_,
        v_a_7687_,
        v_a_7688_,
        v_a_7689_,
        v_a_7690_,
        v_a_7691_,
        v_a_7692_,
        v_a_7693_,
    );
    leanh::lean_dec(v_a_7693_);
    leanh::lean_dec_ref(v_a_7692_);
    leanh::lean_dec(v_a_7691_);
    leanh::lean_dec_ref(v_a_7690_);
    leanh::lean_dec(v_a_7689_);
    leanh::lean_dec(v_a_7688_);
    leanh::lean_dec_ref(v_a_7687_);
    return v_res_7696_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_7700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7700_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__2;
    v___x_7701_ = leanh::lean_unsigned_to_nat(27);
    v___x_7702_ = leanh::lean_unsigned_to_nat(1956);
    v___x_7703_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__1;
    v___x_7704_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__0;
    v___x_7705_ = l_mkPanicMessageWithDecl(
        v___x_7704_,
        v___x_7703_,
        v___x_7702_,
        v___x_7701_,
        v___x_7700_,
    );
    return v___x_7705_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(
    mut v_fst_7706_: u8,
    mut v_fvars_7707_: *mut leanh::LeanObject,
    mut v_b_7708_: *mut leanh::LeanObject,
    mut v___x_7709_: u8,
    mut v_e_7710_: *mut leanh::LeanObject,
    mut v_a_7711_: *mut leanh::LeanObject,
    mut v_a_7712_: *mut leanh::LeanObject,
    mut v_isLet_7713_: u8,
    mut v_topLevel_7714_: u8,
    mut v_x_7715_: *mut leanh::LeanObject,
    mut v___y_7716_: *mut leanh::LeanObject,
    mut v___y_7717_: *mut leanh::LeanObject,
    mut v___y_7718_: *mut leanh::LeanObject,
    mut v___y_7719_: *mut leanh::LeanObject,
    mut v___y_7720_: *mut leanh::LeanObject,
    mut v___y_7721_: *mut leanh::LeanObject,
    mut v___y_7722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7730_: u8 = 0;
    let mut v_declName_7731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_7734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_7735_: u8 = 0;
    let mut v___x_7736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7741_: u8 = 0;
    let mut v___x_7742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7746_: usize = 0;
    let mut v___x_7747_: usize = 0;
    let mut v___x_7748_: u8 = 0;
    let mut v___x_7749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7756_: usize = 0;
    let mut v___x_7757_: usize = 0;
    let mut v___x_7758_: u8 = 0;
    let mut v___x_7759_: usize = 0;
    let mut v___x_7760_: usize = 0;
    let mut v___x_7761_: u8 = 0;
    let mut v_isSharedCheck_7762_: u8 = 0;
    let mut v___x_7764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7765_: u8 = 0;
    let mut v___x_7766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7771_: u8 = 0;
    let mut v_unused_7772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7782_: u8 = 0;
    let mut v___x_7784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7786_: u8 = 0;
    let mut v_a_7787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7790_: u8 = 0;
    let mut v___x_7792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7794_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_fst_7706_ == 0 {
                    leanh::lean_inc_ref(v_x_7715_);
                    v___x_7724_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7724_, 0, v_x_7715_);
                    leanh::lean_ctor_set(v___x_7724_, 1, v_fvars_7707_);
                    v___x_7725_ = lean_expr_instantiate1(v_b_7708_, v_x_7715_);
                    v___x_7726_ = l_Lean_Meta_ExtractLets_extractCore(
                        v___x_7724_,
                        v___x_7725_,
                        v___x_7709_,
                        v___y_7716_,
                        v___y_7717_,
                        v___y_7718_,
                        v___y_7719_,
                        v___y_7720_,
                        v___y_7721_,
                        v___y_7722_,
                    );
                    if leanh::lean_obj_tag(v___x_7726_) == 0 {
                        if leanh::lean_obj_tag(v_e_7710_) == 8 {
                            v_a_7727_ = leanh::lean_ctor_get(v___x_7726_, 0);
                            v_isSharedCheck_7762_ =
                                (!leanh::lean_is_exclusive(v___x_7726_)) as u8;
                            if v_isSharedCheck_7762_ == 0 {
                                v___x_7729_ = v___x_7726_;
                                v_isShared_7730_ = v_isSharedCheck_7762_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7727_);
                                leanh::lean_dec(v___x_7726_);
                                v___x_7729_ = leanh::lean_box(0);
                                v_isShared_7730_ = v_isSharedCheck_7762_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_x_7715_);
                            leanh::lean_dec_ref(v_a_7712_);
                            leanh::lean_dec_ref(v_a_7711_);
                            leanh::lean_dec_ref(v_e_7710_);
                            v_isSharedCheck_7771_ =
                                (!leanh::lean_is_exclusive(v___x_7726_)) as u8;
                            if v_isSharedCheck_7771_ == 0 {
                                v_unused_7772_ = leanh::lean_ctor_get(v___x_7726_, 0);
                                leanh::lean_dec(v_unused_7772_);
                                v___x_7764_ = v___x_7726_;
                                v_isShared_7765_ = v_isSharedCheck_7771_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_7726_);
                                v___x_7764_ = leanh::lean_box(0);
                                v_isShared_7765_ = v_isSharedCheck_7771_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_x_7715_);
                        leanh::lean_dec_ref(v_a_7712_);
                        leanh::lean_dec_ref(v_a_7711_);
                        leanh::lean_dec_ref(v_e_7710_);
                        return v___x_7726_;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_7712_);
                    leanh::lean_dec_ref(v_a_7711_);
                    leanh::lean_dec_ref(v_e_7710_);
                    v___x_7773_ = l_Lean_Expr_fvarId_x21(v_x_7715_);
                    v___x_7774_ = l_Lean_FVarId_getDecl___redArg(
                        v___x_7773_,
                        v___y_7719_,
                        v___y_7721_,
                        v___y_7722_,
                    );
                    if leanh::lean_obj_tag(v___x_7774_) == 0 {
                        v_a_7775_ = leanh::lean_ctor_get(v___x_7774_, 0);
                        leanh::lean_inc(v_a_7775_);
                        leanh::lean_dec_ref_known(v___x_7774_, 1);
                        v___x_7776_ = l_Lean_Meta_ExtractLets_addDecl___redArg(
                            v_a_7775_,
                            v_isLet_7713_,
                            v___y_7716_,
                            v___y_7718_,
                        );
                        if leanh::lean_obj_tag(v___x_7776_) == 0 {
                            leanh::lean_dec_ref_known(v___x_7776_, 1);
                            v___x_7777_ = lean_expr_instantiate1(v_b_7708_, v_x_7715_);
                            leanh::lean_dec_ref(v_x_7715_);
                            v___x_7778_ = l_Lean_Meta_ExtractLets_extractCore(
                                v_fvars_7707_,
                                v___x_7777_,
                                v_topLevel_7714_,
                                v___y_7716_,
                                v___y_7717_,
                                v___y_7718_,
                                v___y_7719_,
                                v___y_7720_,
                                v___y_7721_,
                                v___y_7722_,
                            );
                            return v___x_7778_;
                        } else {
                            leanh::lean_dec_ref(v_x_7715_);
                            leanh::lean_dec(v_fvars_7707_);
                            v_a_7779_ = leanh::lean_ctor_get(v___x_7776_, 0);
                            v_isSharedCheck_7786_ =
                                (!leanh::lean_is_exclusive(v___x_7776_)) as u8;
                            if v_isSharedCheck_7786_ == 0 {
                                v___x_7781_ = v___x_7776_;
                                v_isShared_7782_ = v_isSharedCheck_7786_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7779_);
                                leanh::lean_dec(v___x_7776_);
                                v___x_7781_ = leanh::lean_box(0);
                                v_isShared_7782_ = v_isSharedCheck_7786_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_x_7715_);
                        leanh::lean_dec(v_fvars_7707_);
                        v_a_7787_ = leanh::lean_ctor_get(v___x_7774_, 0);
                        v_isSharedCheck_7794_ =
                            (!leanh::lean_is_exclusive(v___x_7774_)) as u8;
                        if v_isSharedCheck_7794_ == 0 {
                            v___x_7789_ = v___x_7774_;
                            v_isShared_7790_ = v_isSharedCheck_7794_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7787_);
                            leanh::lean_dec(v___x_7774_);
                            v___x_7789_ = leanh::lean_box(0);
                            v_isShared_7790_ = v_isSharedCheck_7794_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_declName_7731_ = leanh::lean_ctor_get(v_e_7710_, 0);
                v_type_7732_ = leanh::lean_ctor_get(v_e_7710_, 1);
                v_value_7733_ = leanh::lean_ctor_get(v_e_7710_, 2);
                v_body_7734_ = leanh::lean_ctor_get(v_e_7710_, 3);
                v_nondep_7735_ = leanh::lean_ctor_get_uint8(
                    v_e_7710_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                );
                v___x_7736_ = leanh::lean_unsigned_to_nat(1);
                v___x_7737_ = lean_mk_empty_array_with_capacity(v___x_7736_);
                v___x_7738_ = lean_array_push(v___x_7737_, v_x_7715_);
                v___x_7739_ = lean_expr_abstract(v_a_7727_, v___x_7738_);
                leanh::lean_dec_ref(v___x_7738_);
                leanh::lean_dec(v_a_7727_);
                v___x_7756_ = lean_ptr_addr(v_type_7732_);
                v___x_7757_ = lean_ptr_addr(v_a_7711_);
                v___x_7758_ = lean_usize_dec_eq(v___x_7756_, v___x_7757_);
                if v___x_7758_ == 0 {
                    v___y_7741_ = v___x_7758_;
                    state = 2;
                    continue;
                } else {
                    v___x_7759_ = lean_ptr_addr(v_value_7733_);
                    v___x_7760_ = lean_ptr_addr(v_a_7712_);
                    v___x_7761_ = lean_usize_dec_eq(v___x_7759_, v___x_7760_);
                    v___y_7741_ = v___x_7761_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_7741_ == 0 {
                    leanh::lean_inc(v_declName_7731_);
                    leanh::lean_dec_ref_known(v_e_7710_, 4);
                    v___x_7742_ = l_Lean_Expr_letE___override(
                        v_declName_7731_,
                        v_a_7711_,
                        v_a_7712_,
                        v___x_7739_,
                        v_nondep_7735_,
                    );
                    if v_isShared_7730_ == 0 {
                        leanh::lean_ctor_set(v___x_7729_, 0, v___x_7742_);
                        v___x_7744_ = v___x_7729_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7745_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7745_, 0, v___x_7742_);
                        v___x_7744_ = v_reuseFailAlloc_7745_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_7746_ = lean_ptr_addr(v_body_7734_);
                    v___x_7747_ = lean_ptr_addr(v___x_7739_);
                    v___x_7748_ = lean_usize_dec_eq(v___x_7746_, v___x_7747_);
                    if v___x_7748_ == 0 {
                        leanh::lean_inc(v_declName_7731_);
                        leanh::lean_dec_ref_known(v_e_7710_, 4);
                        v___x_7749_ = l_Lean_Expr_letE___override(
                            v_declName_7731_,
                            v_a_7711_,
                            v_a_7712_,
                            v___x_7739_,
                            v_nondep_7735_,
                        );
                        if v_isShared_7730_ == 0 {
                            leanh::lean_ctor_set(v___x_7729_, 0, v___x_7749_);
                            v___x_7751_ = v___x_7729_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_7752_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7752_, 0, v___x_7749_);
                            v___x_7751_ = v_reuseFailAlloc_7752_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_7739_);
                        leanh::lean_dec_ref(v_a_7712_);
                        leanh::lean_dec_ref(v_a_7711_);
                        if v_isShared_7730_ == 0 {
                            leanh::lean_ctor_set(v___x_7729_, 0, v_e_7710_);
                            v___x_7754_ = v___x_7729_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_7755_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7755_, 0, v_e_7710_);
                            v___x_7754_ = v_reuseFailAlloc_7755_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_7744_;
            }
            4 => {
                return v___x_7751_;
            }
            5 => {
                return v___x_7754_;
            }
            6 => {
                v___x_7766_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
                v___x_7767_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_7766_);
                if v_isShared_7765_ == 0 {
                    leanh::lean_ctor_set(v___x_7764_, 0, v___x_7767_);
                    v___x_7769_ = v___x_7764_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7770_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7770_, 0, v___x_7767_);
                    v___x_7769_ = v_reuseFailAlloc_7770_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7769_;
            }
            8 => {
                if v_isShared_7782_ == 0 {
                    v___x_7784_ = v___x_7781_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7785_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7785_, 0, v_a_7779_);
                    v___x_7784_ = v_reuseFailAlloc_7785_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7784_;
            }
            10 => {
                if v_isShared_7790_ == 0 {
                    v___x_7792_ = v___x_7789_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7793_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7793_, 0, v_a_7787_);
                    v___x_7792_ = v_reuseFailAlloc_7793_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_7792_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_7795_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_fvars_7796_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_b_7797_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_7798_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_e_7799_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_a_7800_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_a_7801_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_isLet_7802_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_topLevel_7803_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_x_7804_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_7805_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_7806_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_7807_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_7808_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_7809_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_7810_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_7811_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_7812_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_fst_51655__boxed_7813_: u8 = 0;
    let mut v___x_51656__boxed_7814_: u8 = 0;
    let mut v_isLet_boxed_7815_: u8 = 0;
    let mut v_topLevel_boxed_7816_: u8 = 0;
    let mut v_res_7817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_51655__boxed_7813_ = (leanh::lean_unbox(v_fst_7795_) as u8);
    v___x_51656__boxed_7814_ = (leanh::lean_unbox(v___x_7798_) as u8);
    v_isLet_boxed_7815_ = (leanh::lean_unbox(v_isLet_7802_) as u8);
    v_topLevel_boxed_7816_ = (leanh::lean_unbox(v_topLevel_7803_) as u8);
    v_res_7817_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0(v_fst_51655__boxed_7813_, v_fvars_7796_, v_b_7797_, v___x_51656__boxed_7814_, v_e_7799_, v_a_7800_, v_a_7801_, v_isLet_boxed_7815_, v_topLevel_boxed_7816_, v_x_7804_, v___y_7805_, v___y_7806_, v___y_7807_, v___y_7808_, v___y_7809_, v___y_7810_, v___y_7811_);
    leanh::lean_dec(v___y_7811_);
    leanh::lean_dec_ref(v___y_7810_);
    leanh::lean_dec(v___y_7809_);
    leanh::lean_dec_ref(v___y_7808_);
    leanh::lean_dec(v___y_7807_);
    leanh::lean_dec(v___y_7806_);
    leanh::lean_dec_ref(v___y_7805_);
    leanh::lean_dec_ref(v_b_7797_);
    return v_res_7817_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(
    mut v_fvars_7818_: *mut leanh::LeanObject,
    mut v_e_7819_: *mut leanh::LeanObject,
    mut v_isLet_7820_: u8,
    mut v_n_7821_: *mut leanh::LeanObject,
    mut v_t_7822_: *mut leanh::LeanObject,
    mut v_v_7823_: *mut leanh::LeanObject,
    mut v_b_7824_: *mut leanh::LeanObject,
    mut v_topLevel_7825_: u8,
    mut v_a_7826_: *mut leanh::LeanObject,
    mut v_a_7827_: *mut leanh::LeanObject,
    mut v_a_7828_: *mut leanh::LeanObject,
    mut v_a_7829_: *mut leanh::LeanObject,
    mut v_a_7830_: *mut leanh::LeanObject,
    mut v_a_7831_: *mut leanh::LeanObject,
    mut v_a_7832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_7835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7848_: u8 = 0;
    let mut v___x_7849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7853_: u8 = 0;
    let mut v___x_7854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7858_: u8 = 0;
    let mut v___y_7860_: u8 = 0;
    let mut v___y_7861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7863_: u8 = 0;
    let mut v___x_7864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7868_: usize = 0;
    let mut v___x_7869_: usize = 0;
    let mut v___x_7870_: u8 = 0;
    let mut v___x_7871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_7879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_7882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_7883_: u8 = 0;
    let mut v___x_7884_: usize = 0;
    let mut v___x_7885_: usize = 0;
    let mut v___x_7886_: u8 = 0;
    let mut v___x_7887_: usize = 0;
    let mut v___x_7888_: usize = 0;
    let mut v___x_7889_: u8 = 0;
    let mut v___x_7890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7905_: u8 = 0;
    let mut v___x_7906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descend_7907_: u8 = 0;
    let mut v_underBinder_7908_: u8 = 0;
    let mut v_usedOnly_7909_: u8 = 0;
    let mut v_merge_7910_: u8 = 0;
    let mut v_lift_7911_: u8 = 0;
    let mut v___y_7913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7923_: u8 = 0;
    let mut v___y_7924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7939_: u8 = 0;
    let mut v_a_7940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7943_: u8 = 0;
    let mut v___x_7945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7947_: u8 = 0;
    let mut v___y_7949_: u8 = 0;
    let mut v___x_7950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_valueMap_7951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7960_: u8 = 0;
    let mut v___x_7962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7964_: u8 = 0;
    let mut v___x_7965_: u8 = 0;
    let mut v___x_7966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7967_: u8 = 0;
    let mut v_isSharedCheck_7968_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7848_ = 0;
                leanh::lean_inc(v_fvars_7818_);
                v___x_7849_ = l_Lean_Meta_ExtractLets_extractCore(
                    v_fvars_7818_,
                    v_t_7822_,
                    v___x_7848_,
                    v_a_7826_,
                    v_a_7827_,
                    v_a_7828_,
                    v_a_7829_,
                    v_a_7830_,
                    v_a_7831_,
                    v_a_7832_,
                );
                if leanh::lean_obj_tag(v___x_7849_) == 0 {
                    v_a_7850_ = leanh::lean_ctor_get(v___x_7849_, 0);
                    v_isSharedCheck_7968_ = (!leanh::lean_is_exclusive(v___x_7849_)) as u8;
                    if v_isSharedCheck_7968_ == 0 {
                        v___x_7852_ = v___x_7849_;
                        v_isShared_7853_ = v_isSharedCheck_7968_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7850_);
                        leanh::lean_dec(v___x_7849_);
                        v___x_7852_ = leanh::lean_box(0);
                        v_isShared_7853_ = v_isSharedCheck_7968_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_b_7824_);
                    leanh::lean_dec_ref(v_v_7823_);
                    leanh::lean_dec(v_n_7821_);
                    leanh::lean_dec_ref(v_e_7819_);
                    leanh::lean_dec(v_fvars_7818_);
                    return v___x_7849_;
                }
            }
            1 => {
                leanh::lean_inc(v___y_7835_);
                v___x_7843_ = l_Lean_Expr_fvar___override(v___y_7835_);
                v___x_7844_ = lean_expr_instantiate1(v_b_7824_, v___x_7843_);
                leanh::lean_dec_ref(v___x_7843_);
                leanh::lean_dec_ref(v_b_7824_);
                v___x_7845_ = leanh::lean_box((v_topLevel_7825_) as usize);
                v___x_7846_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_ExtractLets_extractCore___boxed as *mut core::ffi::c_void,
                    11,
                    3,
                );
                leanh::lean_closure_set(v___x_7846_, 0, v_fvars_7818_);
                leanh::lean_closure_set(v___x_7846_, 1, v___x_7844_);
                leanh::lean_closure_set(v___x_7846_, 2, v___x_7845_);
                v___x_7847_ = l_Lean_Meta_ExtractLets_withDeclInContext___redArg(
                    v___y_7835_,
                    v___x_7846_,
                    v___y_7836_,
                    v___y_7837_,
                    v___y_7838_,
                    v___y_7839_,
                    v___y_7840_,
                    v___y_7841_,
                    v___y_7842_,
                );
                leanh::lean_dec(v___y_7835_);
                return v___x_7847_;
            }
            2 => {
                leanh::lean_inc(v_fvars_7818_);
                v___x_7854_ = l_Lean_Meta_ExtractLets_extractCore(
                    v_fvars_7818_,
                    v_v_7823_,
                    v___x_7848_,
                    v_a_7826_,
                    v_a_7827_,
                    v_a_7828_,
                    v_a_7829_,
                    v_a_7830_,
                    v_a_7831_,
                    v_a_7832_,
                );
                if leanh::lean_obj_tag(v___x_7854_) == 0 {
                    v_a_7855_ = leanh::lean_ctor_get(v___x_7854_, 0);
                    v_isSharedCheck_7967_ = (!leanh::lean_is_exclusive(v___x_7854_)) as u8;
                    if v_isSharedCheck_7967_ == 0 {
                        v___x_7857_ = v___x_7854_;
                        v_isShared_7858_ = v_isSharedCheck_7967_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7855_);
                        leanh::lean_dec(v___x_7854_);
                        v___x_7857_ = leanh::lean_box(0);
                        v_isShared_7858_ = v_isSharedCheck_7967_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7852_);
                    leanh::lean_dec(v_a_7850_);
                    leanh::lean_dec_ref(v_b_7824_);
                    leanh::lean_dec(v_n_7821_);
                    leanh::lean_dec_ref(v_e_7819_);
                    leanh::lean_dec(v_fvars_7818_);
                    return v___x_7854_;
                }
            }
            3 => {
                v_descend_7907_ = leanh::lean_ctor_get_uint8(v_a_7826_, 3 as u32);
                v_underBinder_7908_ = leanh::lean_ctor_get_uint8(v_a_7826_, 4 as u32);
                v_usedOnly_7909_ = leanh::lean_ctor_get_uint8(v_a_7826_, 5 as u32);
                v_merge_7910_ = leanh::lean_ctor_get_uint8(v_a_7826_, 6 as u32);
                v_lift_7911_ = leanh::lean_ctor_get_uint8(v_a_7826_, 10 as u32);
                if v_usedOnly_7909_ == 0 {
                    v___y_7949_ = v___x_7848_;
                    state = 15;
                    continue;
                } else {
                    v___x_7965_ = l_Lean_Expr_hasLooseBVars(v_b_7824_);
                    if v___x_7965_ == 0 {
                        leanh::lean_del_object(v___x_7857_);
                        leanh::lean_dec(v_a_7855_);
                        leanh::lean_del_object(v___x_7852_);
                        leanh::lean_dec(v_a_7850_);
                        leanh::lean_dec(v_n_7821_);
                        leanh::lean_dec_ref(v_e_7819_);
                        v___x_7966_ = l_Lean_Meta_ExtractLets_extractCore(
                            v_fvars_7818_,
                            v_b_7824_,
                            v_topLevel_7825_,
                            v_a_7826_,
                            v_a_7827_,
                            v_a_7828_,
                            v_a_7829_,
                            v_a_7830_,
                            v_a_7831_,
                            v_a_7832_,
                        );
                        return v___x_7966_;
                    } else {
                        v___y_7949_ = v___x_7848_;
                        state = 15;
                        continue;
                    }
                }
            }
            4 => {
                if v___y_7863_ == 0 {
                    leanh::lean_dec_ref(v___y_7862_);
                    leanh::lean_dec_ref(v_e_7819_);
                    v___x_7864_ = l_Lean_Expr_letE___override(
                        v___y_7861_,
                        v_a_7850_,
                        v_a_7855_,
                        v_b_7824_,
                        v___y_7860_,
                    );
                    if v_isShared_7858_ == 0 {
                        leanh::lean_ctor_set(v___x_7857_, 0, v___x_7864_);
                        v___x_7866_ = v___x_7857_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7867_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7867_, 0, v___x_7864_);
                        v___x_7866_ = v_reuseFailAlloc_7867_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_7868_ = lean_ptr_addr(v___y_7862_);
                    leanh::lean_dec_ref(v___y_7862_);
                    v___x_7869_ = lean_ptr_addr(v_b_7824_);
                    v___x_7870_ = lean_usize_dec_eq(v___x_7868_, v___x_7869_);
                    if v___x_7870_ == 0 {
                        leanh::lean_dec_ref(v_e_7819_);
                        v___x_7871_ = l_Lean_Expr_letE___override(
                            v___y_7861_,
                            v_a_7850_,
                            v_a_7855_,
                            v_b_7824_,
                            v___y_7860_,
                        );
                        if v_isShared_7858_ == 0 {
                            leanh::lean_ctor_set(v___x_7857_, 0, v___x_7871_);
                            v___x_7873_ = v___x_7857_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_7874_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7874_, 0, v___x_7871_);
                            v___x_7873_ = v_reuseFailAlloc_7874_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___y_7861_);
                        leanh::lean_dec(v_a_7855_);
                        leanh::lean_dec(v_a_7850_);
                        leanh::lean_dec_ref(v_b_7824_);
                        if v_isShared_7858_ == 0 {
                            leanh::lean_ctor_set(v___x_7857_, 0, v_e_7819_);
                            v___x_7876_ = v___x_7857_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_7877_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7877_, 0, v_e_7819_);
                            v___x_7876_ = v_reuseFailAlloc_7877_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_7866_;
            }
            6 => {
                return v___x_7873_;
            }
            7 => {
                return v___x_7876_;
            }
            8 => {
                if leanh::lean_obj_tag(v_e_7819_) == 8 {
                    leanh::lean_del_object(v___x_7852_);
                    v_declName_7879_ = leanh::lean_ctor_get(v_e_7819_, 0);
                    v_type_7880_ = leanh::lean_ctor_get(v_e_7819_, 1);
                    v_value_7881_ = leanh::lean_ctor_get(v_e_7819_, 2);
                    v_body_7882_ = leanh::lean_ctor_get(v_e_7819_, 3);
                    v_nondep_7883_ = leanh::lean_ctor_get_uint8(
                        v_e_7819_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    v___x_7884_ = lean_ptr_addr(v_type_7880_);
                    v___x_7885_ = lean_ptr_addr(v_a_7850_);
                    v___x_7886_ = lean_usize_dec_eq(v___x_7884_, v___x_7885_);
                    if v___x_7886_ == 0 {
                        leanh::lean_inc_ref(v_body_7882_);
                        leanh::lean_inc(v_declName_7879_);
                        v___y_7860_ = v_nondep_7883_;
                        v___y_7861_ = v_declName_7879_;
                        v___y_7862_ = v_body_7882_;
                        v___y_7863_ = v___x_7886_;
                        state = 4;
                        continue;
                    } else {
                        v___x_7887_ = lean_ptr_addr(v_value_7881_);
                        v___x_7888_ = lean_ptr_addr(v_a_7855_);
                        v___x_7889_ = lean_usize_dec_eq(v___x_7887_, v___x_7888_);
                        leanh::lean_inc_ref(v_body_7882_);
                        leanh::lean_inc(v_declName_7879_);
                        v___y_7860_ = v_nondep_7883_;
                        v___y_7861_ = v_declName_7879_;
                        v___y_7862_ = v_body_7882_;
                        v___y_7863_ = v___x_7889_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7857_);
                    leanh::lean_dec(v_a_7855_);
                    leanh::lean_dec(v_a_7850_);
                    leanh::lean_dec_ref(v_b_7824_);
                    leanh::lean_dec_ref(v_e_7819_);
                    v___x_7890_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___closed__3);
                    v___x_7891_ = l_panic___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__9(v___x_7890_);
                    if v_isShared_7853_ == 0 {
                        leanh::lean_ctor_set(v___x_7852_, 0, v___x_7891_);
                        v___x_7893_ = v___x_7852_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_7894_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7894_, 0, v___x_7891_);
                        v___x_7893_ = v_reuseFailAlloc_7894_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_7893_;
            }
            10 => {
                v___x_7905_ = 0;
                v___x_7906_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v___y_7901_, v_a_7850_, v_a_7855_, v___y_7897_, v___x_7848_, v___x_7905_, v___y_7900_, v___y_7896_, v___y_7898_, v___y_7899_, v___y_7903_, v___y_7904_, v___y_7902_);
                return v___x_7906_;
            }
            11 => {
                if v_underBinder_7908_ == 0 {
                    leanh::lean_dec(v___y_7918_);
                    leanh::lean_dec_ref(v___y_7914_);
                    state = 8;
                    continue;
                } else {
                    if v_descend_7907_ == 0 {
                        leanh::lean_dec(v___y_7918_);
                        leanh::lean_dec_ref(v___y_7914_);
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_7857_);
                        leanh::lean_del_object(v___x_7852_);
                        leanh::lean_dec_ref(v_b_7824_);
                        leanh::lean_dec_ref(v_e_7819_);
                        v___y_7896_ = v___y_7913_;
                        v___y_7897_ = v___y_7914_;
                        v___y_7898_ = v___y_7915_;
                        v___y_7899_ = v___y_7917_;
                        v___y_7900_ = v___y_7916_;
                        v___y_7901_ = v___y_7918_;
                        v___y_7902_ = v___y_7920_;
                        v___y_7903_ = v___y_7919_;
                        v___y_7904_ = v___y_7921_;
                        state = 10;
                        continue;
                    }
                }
            }
            12 => {
                leanh::lean_inc(v_a_7855_);
                leanh::lean_inc(v_a_7850_);
                v___x_7931_ = l_Lean_Meta_ExtractLets_isExtractableLet___redArg(
                    v_fvars_7818_,
                    v_n_7821_,
                    v_a_7850_,
                    v_a_7855_,
                    v___y_7924_,
                    v___y_7926_,
                    v___y_7929_,
                    v___y_7930_,
                );
                if leanh::lean_obj_tag(v___x_7931_) == 0 {
                    v_a_7932_ = leanh::lean_ctor_get(v___x_7931_, 0);
                    leanh::lean_inc(v_a_7932_);
                    leanh::lean_dec_ref_known(v___x_7931_, 1);
                    v_fst_7933_ = leanh::lean_ctor_get(v_a_7932_, 0);
                    leanh::lean_inc_n(v_fst_7933_, 2);
                    v_snd_7934_ = leanh::lean_ctor_get(v_a_7932_, 1);
                    leanh::lean_inc(v_snd_7934_);
                    leanh::lean_dec(v_a_7932_);
                    v___x_7935_ = leanh::lean_box((v___x_7848_) as usize);
                    v___x_7936_ = leanh::lean_box((v_isLet_7820_) as usize);
                    v___x_7937_ = leanh::lean_box((v_topLevel_7825_) as usize);
                    leanh::lean_inc(v_a_7855_);
                    leanh::lean_inc(v_a_7850_);
                    leanh::lean_inc_ref(v_e_7819_);
                    leanh::lean_inc_ref(v_b_7824_);
                    v___f_7938_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___lam__0___boxed as *mut core::ffi::c_void, 18, 9);
                    leanh::lean_closure_set(v___f_7938_, 0, v_fst_7933_);
                    leanh::lean_closure_set(v___f_7938_, 1, v_fvars_7818_);
                    leanh::lean_closure_set(v___f_7938_, 2, v_b_7824_);
                    leanh::lean_closure_set(v___f_7938_, 3, v___x_7935_);
                    leanh::lean_closure_set(v___f_7938_, 4, v_e_7819_);
                    leanh::lean_closure_set(v___f_7938_, 5, v_a_7850_);
                    leanh::lean_closure_set(v___f_7938_, 6, v_a_7855_);
                    leanh::lean_closure_set(v___f_7938_, 7, v___x_7936_);
                    leanh::lean_closure_set(v___f_7938_, 8, v___x_7937_);
                    v___x_7939_ = (leanh::lean_unbox(v_fst_7933_) as u8);
                    leanh::lean_dec(v_fst_7933_);
                    if v___x_7939_ == 0 {
                        v___y_7913_ = v___y_7925_;
                        v___y_7914_ = v___f_7938_;
                        v___y_7915_ = v___y_7926_;
                        v___y_7916_ = v___y_7924_;
                        v___y_7917_ = v___y_7927_;
                        v___y_7918_ = v_snd_7934_;
                        v___y_7919_ = v___y_7928_;
                        v___y_7920_ = v___y_7930_;
                        v___y_7921_ = v___y_7929_;
                        state = 11;
                        continue;
                    } else {
                        if v___y_7923_ == 0 {
                            leanh::lean_del_object(v___x_7857_);
                            leanh::lean_del_object(v___x_7852_);
                            leanh::lean_dec_ref(v_b_7824_);
                            leanh::lean_dec_ref(v_e_7819_);
                            v___y_7896_ = v___y_7925_;
                            v___y_7897_ = v___f_7938_;
                            v___y_7898_ = v___y_7926_;
                            v___y_7899_ = v___y_7927_;
                            v___y_7900_ = v___y_7924_;
                            v___y_7901_ = v_snd_7934_;
                            v___y_7902_ = v___y_7930_;
                            v___y_7903_ = v___y_7928_;
                            v___y_7904_ = v___y_7929_;
                            state = 10;
                            continue;
                        } else {
                            v___y_7913_ = v___y_7925_;
                            v___y_7914_ = v___f_7938_;
                            v___y_7915_ = v___y_7926_;
                            v___y_7916_ = v___y_7924_;
                            v___y_7917_ = v___y_7927_;
                            v___y_7918_ = v_snd_7934_;
                            v___y_7919_ = v___y_7928_;
                            v___y_7920_ = v___y_7930_;
                            v___y_7921_ = v___y_7929_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_7857_);
                    leanh::lean_dec(v_a_7855_);
                    leanh::lean_del_object(v___x_7852_);
                    leanh::lean_dec(v_a_7850_);
                    leanh::lean_dec_ref(v_b_7824_);
                    leanh::lean_dec_ref(v_e_7819_);
                    leanh::lean_dec(v_fvars_7818_);
                    v_a_7940_ = leanh::lean_ctor_get(v___x_7931_, 0);
                    v_isSharedCheck_7947_ = (!leanh::lean_is_exclusive(v___x_7931_)) as u8;
                    if v_isSharedCheck_7947_ == 0 {
                        v___x_7942_ = v___x_7931_;
                        v_isShared_7943_ = v_isSharedCheck_7947_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7940_);
                        leanh::lean_dec(v___x_7931_);
                        v___x_7942_ = leanh::lean_box(0);
                        v_isShared_7943_ = v_isSharedCheck_7947_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                if v_isShared_7943_ == 0 {
                    v___x_7945_ = v___x_7942_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7946_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7946_, 0, v_a_7940_);
                    v___x_7945_ = v_reuseFailAlloc_7946_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7945_;
            }
            15 => {
                if v_merge_7910_ == 0 {
                    v___y_7923_ = v___y_7949_;
                    v___y_7924_ = v_a_7826_;
                    v___y_7925_ = v_a_7827_;
                    v___y_7926_ = v_a_7828_;
                    v___y_7927_ = v_a_7829_;
                    v___y_7928_ = v_a_7830_;
                    v___y_7929_ = v_a_7831_;
                    v___y_7930_ = v_a_7832_;
                    state = 12;
                    continue;
                } else {
                    v___x_7950_ = lean_st_ref_get(v_a_7828_);
                    v_valueMap_7951_ = leanh::lean_ctor_get(v___x_7950_, 2);
                    leanh::lean_inc_ref(v_valueMap_7951_);
                    leanh::lean_dec(v___x_7950_);
                    v___x_7952_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_valueMap_7951_, v_a_7855_);
                    leanh::lean_dec_ref(v_valueMap_7951_);
                    if leanh::lean_obj_tag(v___x_7952_) == 1 {
                        leanh::lean_del_object(v___x_7857_);
                        leanh::lean_dec(v_a_7855_);
                        leanh::lean_del_object(v___x_7852_);
                        leanh::lean_dec(v_a_7850_);
                        leanh::lean_dec(v_n_7821_);
                        leanh::lean_dec_ref(v_e_7819_);
                        if v_isLet_7820_ == 0 {
                            v_val_7953_ = leanh::lean_ctor_get(v___x_7952_, 0);
                            leanh::lean_inc(v_val_7953_);
                            leanh::lean_dec_ref_known(v___x_7952_, 1);
                            v___y_7835_ = v_val_7953_;
                            v___y_7836_ = v_a_7826_;
                            v___y_7837_ = v_a_7827_;
                            v___y_7838_ = v_a_7828_;
                            v___y_7839_ = v_a_7829_;
                            v___y_7840_ = v_a_7830_;
                            v___y_7841_ = v_a_7831_;
                            v___y_7842_ = v_a_7832_;
                            state = 1;
                            continue;
                        } else {
                            if v_lift_7911_ == 0 {
                                v_val_7954_ = leanh::lean_ctor_get(v___x_7952_, 0);
                                leanh::lean_inc(v_val_7954_);
                                leanh::lean_dec_ref_known(v___x_7952_, 1);
                                v___y_7835_ = v_val_7954_;
                                v___y_7836_ = v_a_7826_;
                                v___y_7837_ = v_a_7827_;
                                v___y_7838_ = v_a_7828_;
                                v___y_7839_ = v_a_7829_;
                                v___y_7840_ = v_a_7830_;
                                v___y_7841_ = v_a_7831_;
                                v___y_7842_ = v_a_7832_;
                                state = 1;
                                continue;
                            } else {
                                v_val_7955_ = leanh::lean_ctor_get(v___x_7952_, 0);
                                leanh::lean_inc(v_val_7955_);
                                leanh::lean_dec_ref_known(v___x_7952_, 1);
                                v___x_7956_ = l_Lean_Meta_ExtractLets_ensureIsLet___redArg(
                                    v_val_7955_,
                                    v_a_7828_,
                                );
                                if leanh::lean_obj_tag(v___x_7956_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_7956_, 1);
                                    v___y_7835_ = v_val_7955_;
                                    v___y_7836_ = v_a_7826_;
                                    v___y_7837_ = v_a_7827_;
                                    v___y_7838_ = v_a_7828_;
                                    v___y_7839_ = v_a_7829_;
                                    v___y_7840_ = v_a_7830_;
                                    v___y_7841_ = v_a_7831_;
                                    v___y_7842_ = v_a_7832_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_val_7955_);
                                    leanh::lean_dec_ref(v_b_7824_);
                                    leanh::lean_dec(v_fvars_7818_);
                                    v_a_7957_ = leanh::lean_ctor_get(v___x_7956_, 0);
                                    v_isSharedCheck_7964_ =
                                        (!leanh::lean_is_exclusive(v___x_7956_)) as u8;
                                    if v_isSharedCheck_7964_ == 0 {
                                        v___x_7959_ = v___x_7956_;
                                        v_isShared_7960_ = v_isSharedCheck_7964_;
                                        state = 16;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_7957_);
                                        leanh::lean_dec(v___x_7956_);
                                        v___x_7959_ = leanh::lean_box(0);
                                        v_isShared_7960_ = v_isSharedCheck_7964_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_7952_);
                        v___y_7923_ = v___y_7949_;
                        v___y_7924_ = v_a_7826_;
                        v___y_7925_ = v_a_7827_;
                        v___y_7926_ = v_a_7828_;
                        v___y_7927_ = v_a_7829_;
                        v___y_7928_ = v_a_7830_;
                        v___y_7929_ = v_a_7831_;
                        v___y_7930_ = v_a_7832_;
                        state = 12;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_7960_ == 0 {
                    v___x_7962_ = v___x_7959_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_7963_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7963_, 0, v_a_7957_);
                    v___x_7962_ = v_reuseFailAlloc_7963_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_7962_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed(
    mut v_fvars_7969_: *mut leanh::LeanObject,
    mut v_struct_7970_: *mut leanh::LeanObject,
    mut v___y_7971_: *mut leanh::LeanObject,
    mut v_typeName_7972_: *mut leanh::LeanObject,
    mut v_idx_7973_: *mut leanh::LeanObject,
    mut v_e_7974_: *mut leanh::LeanObject,
    mut v___y_7975_: *mut leanh::LeanObject,
    mut v___y_7976_: *mut leanh::LeanObject,
    mut v___y_7977_: *mut leanh::LeanObject,
    mut v___y_7978_: *mut leanh::LeanObject,
    mut v___y_7979_: *mut leanh::LeanObject,
    mut v___y_7980_: *mut leanh::LeanObject,
    mut v___y_7981_: *mut leanh::LeanObject,
    mut v___y_7982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_51431__boxed_7983_: u8 = 0;
    let mut v_res_7984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_51431__boxed_7983_ = (leanh::lean_unbox(v___y_7971_) as u8);
    v_res_7984_ = l_Lean_Meta_ExtractLets_extractCore___lam__2(
        v_fvars_7969_,
        v_struct_7970_,
        v___y_51431__boxed_7983_,
        v_typeName_7972_,
        v_idx_7973_,
        v_e_7974_,
        v___y_7975_,
        v___y_7976_,
        v___y_7977_,
        v___y_7978_,
        v___y_7979_,
        v___y_7980_,
        v___y_7981_,
    );
    leanh::lean_dec(v___y_7981_);
    leanh::lean_dec_ref(v___y_7980_);
    leanh::lean_dec(v___y_7979_);
    leanh::lean_dec_ref(v___y_7978_);
    leanh::lean_dec(v___y_7977_);
    leanh::lean_dec(v___y_7976_);
    leanh::lean_dec_ref(v___y_7975_);
    return v_res_7984_;
}
pub unsafe fn _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_7988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7988_ = l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__3;
    v___x_7989_ = leanh::lean_unsigned_to_nat(75);
    v___x_7990_ = leanh::lean_unsigned_to_nat(229);
    v___x_7991_ = l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__2;
    v___x_7992_ = l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__1;
    v___x_7993_ = l_mkPanicMessageWithDecl(
        v___x_7992_,
        v___x_7991_,
        v___x_7990_,
        v___x_7989_,
        v___x_7988_,
    );
    return v___x_7993_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_extractCore___lam__3(
    mut v_descend_7994_: u8,
    mut v_e_7995_: *mut leanh::LeanObject,
    mut v_fvars_7996_: *mut leanh::LeanObject,
    mut v___x_7997_: u8,
    mut v_topLevel_7998_: u8,
    mut v___y_7999_: u8,
    mut v_____r_8000_: *mut leanh::LeanObject,
    mut v___y_8001_: *mut leanh::LeanObject,
    mut v___y_8002_: *mut leanh::LeanObject,
    mut v___y_8003_: *mut leanh::LeanObject,
    mut v___y_8004_: *mut leanh::LeanObject,
    mut v___y_8005_: *mut leanh::LeanObject,
    mut v___y_8006_: *mut leanh::LeanObject,
    mut v___y_8007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_8010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_8014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_8015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_8021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_8022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_8023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_8024_: u8 = 0;
    let mut v___x_8025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_8029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_8030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_8031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_8032_: u8 = 0;
    let mut v___x_8033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_8037_: u8 = 0;
    let mut v_declName_8038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_8039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_8040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_8041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_8043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_8044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_8045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_8046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_8048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_8049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8054_: u8 = 0;
    let mut v___x_8055_: usize = 0;
    let mut v___x_8056_: usize = 0;
    let mut v___x_8057_: u8 = 0;
    let mut v___x_8058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8065_: u8 = 0;
    let mut v_typeName_8066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_8067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_8068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_7995_) {
                5 => {
                    v___x_8013_ = l_Lean_Expr_getAppFn(v_e_7995_);
                    v_dummy_8014_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0_once
                        ),
                        _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__0,
                    );
                    v_nargs_8015_ = l_Lean_Expr_getAppNumArgs(v_e_7995_);
                    leanh::lean_inc(v_nargs_8015_);
                    v___x_8016_ = lean_mk_array(v_nargs_8015_, v_dummy_8014_);
                    v___x_8017_ = leanh::lean_unsigned_to_nat(1);
                    v___x_8018_ = lean_nat_sub(v_nargs_8015_, v___x_8017_);
                    leanh::lean_dec(v_nargs_8015_);
                    leanh::lean_inc_ref(v_e_7995_);
                    v___x_8019_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_e_7995_,
                        v___x_8016_,
                        v___x_8018_,
                    );
                    v___x_8020_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp___boxed as *mut core::ffi::c_void, 11, 3);
                    leanh::lean_closure_set(v___x_8020_, 0, v_fvars_7996_);
                    leanh::lean_closure_set(v___x_8020_, 1, v___x_8013_);
                    leanh::lean_closure_set(v___x_8020_, 2, v___x_8019_);
                    v_k_8010_ = v___x_8020_;
                    state = 1;
                    continue;
                }
                6 => {
                    v_binderName_8021_ = leanh::lean_ctor_get(v_e_7995_, 0);
                    v_binderType_8022_ = leanh::lean_ctor_get(v_e_7995_, 1);
                    v_body_8023_ = leanh::lean_ctor_get(v_e_7995_, 2);
                    v_binderInfo_8024_ = leanh::lean_ctor_get_uint8(
                        v_e_7995_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    v___x_8025_ = leanh::lean_box((v_binderInfo_8024_) as usize);
                    leanh::lean_inc_ref_n(v_body_8023_, 2);
                    leanh::lean_inc_ref_n(v_binderType_8022_, 2);
                    leanh::lean_inc_ref(v_e_7995_);
                    leanh::lean_inc_n(v_binderName_8021_, 2);
                    v___f_8026_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_ExtractLets_extractCore___lam__0___boxed
                            as *mut core::ffi::c_void,
                        7,
                        5,
                    );
                    leanh::lean_closure_set(v___f_8026_, 0, v_binderName_8021_);
                    leanh::lean_closure_set(v___f_8026_, 1, v___x_8025_);
                    leanh::lean_closure_set(v___f_8026_, 2, v_e_7995_);
                    leanh::lean_closure_set(v___f_8026_, 3, v_binderType_8022_);
                    leanh::lean_closure_set(v___f_8026_, 4, v_body_8023_);
                    v___x_8027_ = leanh::lean_box((v_binderInfo_8024_) as usize);
                    v___x_8028_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed as *mut core::ffi::c_void, 14, 6);
                    leanh::lean_closure_set(v___x_8028_, 0, v_fvars_7996_);
                    leanh::lean_closure_set(v___x_8028_, 1, v_binderName_8021_);
                    leanh::lean_closure_set(v___x_8028_, 2, v_binderType_8022_);
                    leanh::lean_closure_set(v___x_8028_, 3, v_body_8023_);
                    leanh::lean_closure_set(v___x_8028_, 4, v___x_8027_);
                    leanh::lean_closure_set(v___x_8028_, 5, v___f_8026_);
                    v_k_8010_ = v___x_8028_;
                    state = 1;
                    continue;
                }
                7 => {
                    v_binderName_8029_ = leanh::lean_ctor_get(v_e_7995_, 0);
                    v_binderType_8030_ = leanh::lean_ctor_get(v_e_7995_, 1);
                    v_body_8031_ = leanh::lean_ctor_get(v_e_7995_, 2);
                    v_binderInfo_8032_ = leanh::lean_ctor_get_uint8(
                        v_e_7995_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    v___x_8033_ = leanh::lean_box((v_binderInfo_8032_) as usize);
                    leanh::lean_inc_ref_n(v_body_8031_, 2);
                    leanh::lean_inc_ref_n(v_binderType_8030_, 2);
                    leanh::lean_inc_ref(v_e_7995_);
                    leanh::lean_inc_n(v_binderName_8029_, 2);
                    v___f_8034_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_ExtractLets_extractCore___lam__1___boxed
                            as *mut core::ffi::c_void,
                        7,
                        5,
                    );
                    leanh::lean_closure_set(v___f_8034_, 0, v_binderName_8029_);
                    leanh::lean_closure_set(v___f_8034_, 1, v___x_8033_);
                    leanh::lean_closure_set(v___f_8034_, 2, v_e_7995_);
                    leanh::lean_closure_set(v___f_8034_, 3, v_binderType_8030_);
                    leanh::lean_closure_set(v___f_8034_, 4, v_body_8031_);
                    v___x_8035_ = leanh::lean_box((v_binderInfo_8032_) as usize);
                    v___x_8036_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractBinder___boxed as *mut core::ffi::c_void, 14, 6);
                    leanh::lean_closure_set(v___x_8036_, 0, v_fvars_7996_);
                    leanh::lean_closure_set(v___x_8036_, 1, v_binderName_8029_);
                    leanh::lean_closure_set(v___x_8036_, 2, v_binderType_8030_);
                    leanh::lean_closure_set(v___x_8036_, 3, v_body_8031_);
                    leanh::lean_closure_set(v___x_8036_, 4, v___x_8035_);
                    leanh::lean_closure_set(v___x_8036_, 5, v___f_8034_);
                    v_k_8010_ = v___x_8036_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_nondep_8037_ = leanh::lean_ctor_get_uint8(
                        v_e_7995_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    if v_nondep_8037_ == 0 {
                        v_declName_8038_ = leanh::lean_ctor_get(v_e_7995_, 0);
                        leanh::lean_inc(v_declName_8038_);
                        v_type_8039_ = leanh::lean_ctor_get(v_e_7995_, 1);
                        leanh::lean_inc_ref(v_type_8039_);
                        v_value_8040_ = leanh::lean_ctor_get(v_e_7995_, 2);
                        leanh::lean_inc_ref(v_value_8040_);
                        v_body_8041_ = leanh::lean_ctor_get(v_e_7995_, 3);
                        leanh::lean_inc_ref(v_body_8041_);
                        v___x_8042_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_7996_, v_e_7995_, v___x_7997_, v_declName_8038_, v_type_8039_, v_value_8040_, v_body_8041_, v_topLevel_7998_, v___y_8001_, v___y_8002_, v___y_8003_, v___y_8004_, v___y_8005_, v___y_8006_, v___y_8007_);
                        return v___x_8042_;
                    } else {
                        v_declName_8043_ = leanh::lean_ctor_get(v_e_7995_, 0);
                        leanh::lean_inc(v_declName_8043_);
                        v_type_8044_ = leanh::lean_ctor_get(v_e_7995_, 1);
                        leanh::lean_inc_ref(v_type_8044_);
                        v_value_8045_ = leanh::lean_ctor_get(v_e_7995_, 2);
                        leanh::lean_inc_ref(v_value_8045_);
                        v_body_8046_ = leanh::lean_ctor_get(v_e_7995_, 3);
                        leanh::lean_inc_ref(v_body_8046_);
                        v___x_8047_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(v_fvars_7996_, v_e_7995_, v___y_7999_, v_declName_8043_, v_type_8044_, v_value_8045_, v_body_8046_, v_topLevel_7998_, v___y_8001_, v___y_8002_, v___y_8003_, v___y_8004_, v___y_8005_, v___y_8006_, v___y_8007_);
                        return v___x_8047_;
                    }
                }
                10 => {
                    v_data_8048_ = leanh::lean_ctor_get(v_e_7995_, 0);
                    v_expr_8049_ = leanh::lean_ctor_get(v_e_7995_, 1);
                    leanh::lean_inc_ref(v_expr_8049_);
                    v___x_8050_ = l_Lean_Meta_ExtractLets_extractCore(
                        v_fvars_7996_,
                        v_expr_8049_,
                        v_topLevel_7998_,
                        v___y_8001_,
                        v___y_8002_,
                        v___y_8003_,
                        v___y_8004_,
                        v___y_8005_,
                        v___y_8006_,
                        v___y_8007_,
                    );
                    if leanh::lean_obj_tag(v___x_8050_) == 0 {
                        v_a_8051_ = leanh::lean_ctor_get(v___x_8050_, 0);
                        v_isSharedCheck_8065_ =
                            (!leanh::lean_is_exclusive(v___x_8050_)) as u8;
                        if v_isSharedCheck_8065_ == 0 {
                            v___x_8053_ = v___x_8050_;
                            v_isShared_8054_ = v_isSharedCheck_8065_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8051_);
                            leanh::lean_dec(v___x_8050_);
                            v___x_8053_ = leanh::lean_box(0);
                            v_isShared_8054_ = v_isSharedCheck_8065_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_e_7995_, 2);
                        return v___x_8050_;
                    }
                }
                11 => {
                    v_typeName_8066_ = leanh::lean_ctor_get(v_e_7995_, 0);
                    v_idx_8067_ = leanh::lean_ctor_get(v_e_7995_, 1);
                    v_struct_8068_ = leanh::lean_ctor_get(v_e_7995_, 2);
                    v___x_8069_ = leanh::lean_box((v___y_7999_) as usize);
                    leanh::lean_inc_ref(v_e_7995_);
                    leanh::lean_inc(v_idx_8067_);
                    leanh::lean_inc(v_typeName_8066_);
                    leanh::lean_inc_ref(v_struct_8068_);
                    v___f_8070_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_ExtractLets_extractCore___lam__2___boxed
                            as *mut core::ffi::c_void,
                        14,
                        6,
                    );
                    leanh::lean_closure_set(v___f_8070_, 0, v_fvars_7996_);
                    leanh::lean_closure_set(v___f_8070_, 1, v_struct_8068_);
                    leanh::lean_closure_set(v___f_8070_, 2, v___x_8069_);
                    leanh::lean_closure_set(v___f_8070_, 3, v_typeName_8066_);
                    leanh::lean_closure_set(v___f_8070_, 4, v_idx_8067_);
                    leanh::lean_closure_set(v___f_8070_, 5, v_e_7995_);
                    v_k_8010_ = v___f_8070_;
                    state = 1;
                    continue;
                }
                _ => {
                    leanh::lean_dec(v_fvars_7996_);
                    leanh::lean_dec_ref(v_e_7995_);
                    v___x_8071_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4_once
                        ),
                        _init_l_Lean_Meta_ExtractLets_extractCore___lam__3___closed__4,
                    );
                    v___x_8072_ = l_panic___at___00Lean_Meta_ExtractLets_extractCore_spec__4(
                        v___x_8071_,
                        v___y_8001_,
                        v___y_8002_,
                        v___y_8003_,
                        v___y_8004_,
                        v___y_8005_,
                        v___y_8006_,
                        v___y_8007_,
                    );
                    return v___x_8072_;
                }
            },
            1 => {
                if v_descend_7994_ == 0 {
                    leanh::lean_dec_ref(v_k_8010_);
                    v___x_8011_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8011_, 0, v_e_7995_);
                    return v___x_8011_;
                } else {
                    leanh::lean_dec_ref(v_e_7995_);
                    leanh::lean_inc(v___y_8007_);
                    leanh::lean_inc_ref(v___y_8006_);
                    leanh::lean_inc(v___y_8005_);
                    leanh::lean_inc_ref(v___y_8004_);
                    leanh::lean_inc(v___y_8003_);
                    leanh::lean_inc(v___y_8002_);
                    leanh::lean_inc_ref(v___y_8001_);
                    v___x_8012_ = leanh::lean_apply_8(
                        v_k_8010_,
                        v___y_8001_,
                        v___y_8002_,
                        v___y_8003_,
                        v___y_8004_,
                        v___y_8005_,
                        v___y_8006_,
                        v___y_8007_,
                        leanh::lean_box(0),
                    );
                    return v___x_8012_;
                }
            }
            2 => {
                v___x_8055_ = lean_ptr_addr(v_expr_8049_);
                v___x_8056_ = lean_ptr_addr(v_a_8051_);
                v___x_8057_ = lean_usize_dec_eq(v___x_8055_, v___x_8056_);
                if v___x_8057_ == 0 {
                    leanh::lean_inc(v_data_8048_);
                    leanh::lean_dec_ref_known(v_e_7995_, 2);
                    v___x_8058_ = l_Lean_Expr_mdata___override(v_data_8048_, v_a_8051_);
                    if v_isShared_8054_ == 0 {
                        leanh::lean_ctor_set(v___x_8053_, 0, v___x_8058_);
                        v___x_8060_ = v___x_8053_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8061_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8061_, 0, v___x_8058_);
                        v___x_8060_ = v_reuseFailAlloc_8061_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_8051_);
                    if v_isShared_8054_ == 0 {
                        leanh::lean_ctor_set(v___x_8053_, 0, v_e_7995_);
                        v___x_8063_ = v___x_8053_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_8064_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8064_, 0, v_e_7995_);
                        v___x_8063_ = v_reuseFailAlloc_8064_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_8060_;
            }
            4 => {
                return v___x_8063_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed(
    mut v_descend_8073_: *mut leanh::LeanObject,
    mut v_e_8074_: *mut leanh::LeanObject,
    mut v_fvars_8075_: *mut leanh::LeanObject,
    mut v___x_8076_: *mut leanh::LeanObject,
    mut v_topLevel_8077_: *mut leanh::LeanObject,
    mut v___y_8078_: *mut leanh::LeanObject,
    mut v_____r_8079_: *mut leanh::LeanObject,
    mut v___y_8080_: *mut leanh::LeanObject,
    mut v___y_8081_: *mut leanh::LeanObject,
    mut v___y_8082_: *mut leanh::LeanObject,
    mut v___y_8083_: *mut leanh::LeanObject,
    mut v___y_8084_: *mut leanh::LeanObject,
    mut v___y_8085_: *mut leanh::LeanObject,
    mut v___y_8086_: *mut leanh::LeanObject,
    mut v___y_8087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_descend_boxed_8088_: u8 = 0;
    let mut v___x_51584__boxed_8089_: u8 = 0;
    let mut v_topLevel_boxed_8090_: u8 = 0;
    let mut v___y_51585__boxed_8091_: u8 = 0;
    let mut v_res_8092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_descend_boxed_8088_ = (leanh::lean_unbox(v_descend_8073_) as u8);
    v___x_51584__boxed_8089_ = (leanh::lean_unbox(v___x_8076_) as u8);
    v_topLevel_boxed_8090_ = (leanh::lean_unbox(v_topLevel_8077_) as u8);
    v___y_51585__boxed_8091_ = (leanh::lean_unbox(v___y_8078_) as u8);
    v_res_8092_ = l_Lean_Meta_ExtractLets_extractCore___lam__3(
        v_descend_boxed_8088_,
        v_e_8074_,
        v_fvars_8075_,
        v___x_51584__boxed_8089_,
        v_topLevel_boxed_8090_,
        v___y_51585__boxed_8091_,
        v_____r_8079_,
        v___y_8080_,
        v___y_8081_,
        v___y_8082_,
        v___y_8083_,
        v___y_8084_,
        v___y_8085_,
        v___y_8086_,
    );
    leanh::lean_dec(v___y_8086_);
    leanh::lean_dec_ref(v___y_8085_);
    leanh::lean_dec(v___y_8084_);
    leanh::lean_dec_ref(v___y_8083_);
    leanh::lean_dec(v___y_8082_);
    leanh::lean_dec(v___y_8081_);
    leanh::lean_dec_ref(v___y_8080_);
    return v_res_8092_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_extractCore(
    mut v_fvars_8093_: *mut leanh::LeanObject,
    mut v_e_8094_: *mut leanh::LeanObject,
    mut v_topLevel_8095_: u8,
    mut v_a_8096_: *mut leanh::LeanObject,
    mut v_a_8097_: *mut leanh::LeanObject,
    mut v_a_8098_: *mut leanh::LeanObject,
    mut v_a_8099_: *mut leanh::LeanObject,
    mut v_a_8100_: *mut leanh::LeanObject,
    mut v_a_8101_: *mut leanh::LeanObject,
    mut v_a_8102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_8105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8120_: u8 = 0;
    let mut v_proofs_8121_: u8 = 0;
    let mut v_types_8122_: u8 = 0;
    let mut v_descend_8123_: u8 = 0;
    let mut v___y_8125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8129_: u8 = 0;
    let mut v___x_8130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8135_: u8 = 0;
    let mut v___x_8137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8139_: u8 = 0;
    let mut v___x_8140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8143_: u8 = 0;
    let mut v___x_8144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8148_: u8 = 0;
    let mut v___x_8149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8156_: u8 = 0;
    let mut v___x_8157_: u8 = 0;
    let mut v_val_8158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8161_: u8 = 0;
    let mut v___x_8163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8165_: u8 = 0;
    let mut v___x_8167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8120_ = l_Lean_Expr_isAtomic(v_e_8094_);
                if v___x_8120_ == 0 {
                    v_proofs_8121_ = leanh::lean_ctor_get_uint8(v_a_8096_, 0 as u32);
                    v_types_8122_ = leanh::lean_ctor_get_uint8(v_a_8096_, 1 as u32);
                    v_descend_8123_ = leanh::lean_ctor_get_uint8(v_a_8096_, 3 as u32);
                    if v_descend_8123_ == 0 {
                        state = 10;
                        continue;
                    } else {
                        if v___x_8120_ == 0 {
                            v___y_8143_ = v___x_8120_;
                            state = 7;
                            continue;
                        } else {
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fvars_8093_);
                    v___x_8169_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8169_, 0, v_e_8094_);
                    return v___x_8169_;
                }
            }
            1 => {
                v___x_8107_ = lean_st_ref_take(v_a_8097_);
                leanh::lean_inc_ref(v_a_8106_);
                v___x_8108_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v___x_8107_, v___y_8105_, v_a_8106_);
                v___x_8109_ = lean_st_ref_set(v_a_8097_, v___x_8108_);
                v___x_8110_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8110_, 0, v_a_8106_);
                return v___x_8110_;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_8113_) == 0 {
                    v_a_8114_ = leanh::lean_ctor_get(v___y_8113_, 0);
                    leanh::lean_inc(v_a_8114_);
                    leanh::lean_dec_ref_known(v___y_8113_, 1);
                    v___y_8105_ = v___y_8112_;
                    v_a_8106_ = v_a_8114_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_8112_);
                    return v___y_8113_;
                }
            }
            3 => {
                v___x_8118_ = leanh::lean_box(0);
                leanh::lean_inc(v_a_8102_);
                leanh::lean_inc_ref(v_a_8101_);
                leanh::lean_inc(v_a_8100_);
                leanh::lean_inc_ref(v_a_8099_);
                leanh::lean_inc(v_a_8098_);
                leanh::lean_inc(v_a_8097_);
                leanh::lean_inc_ref(v_a_8096_);
                v___x_8119_ = leanh::lean_apply_9(
                    v___y_8117_,
                    v___x_8118_,
                    v_a_8096_,
                    v_a_8097_,
                    v_a_8098_,
                    v_a_8099_,
                    v_a_8100_,
                    v_a_8101_,
                    v_a_8102_,
                    leanh::lean_box(0),
                );
                v___y_8112_ = v___y_8116_;
                v___y_8113_ = v___x_8119_;
                state = 2;
                continue;
            }
            4 => {
                if v_proofs_8121_ == 0 {
                    leanh::lean_inc_ref(v_e_8094_);
                    v___x_8127_ =
                        l_Lean_Meta_isProof(v_e_8094_, v_a_8099_, v_a_8100_, v_a_8101_, v_a_8102_);
                    if leanh::lean_obj_tag(v___x_8127_) == 0 {
                        v_a_8128_ = leanh::lean_ctor_get(v___x_8127_, 0);
                        leanh::lean_inc(v_a_8128_);
                        leanh::lean_dec_ref_known(v___x_8127_, 1);
                        v___x_8129_ = (leanh::lean_unbox(v_a_8128_) as u8);
                        leanh::lean_dec(v_a_8128_);
                        if v___x_8129_ == 0 {
                            leanh::lean_dec_ref(v_e_8094_);
                            v___x_8130_ = leanh::lean_box(0);
                            leanh::lean_inc(v_a_8102_);
                            leanh::lean_inc_ref(v_a_8101_);
                            leanh::lean_inc(v_a_8100_);
                            leanh::lean_inc_ref(v_a_8099_);
                            leanh::lean_inc(v_a_8098_);
                            leanh::lean_inc(v_a_8097_);
                            leanh::lean_inc_ref(v_a_8096_);
                            v___x_8131_ = leanh::lean_apply_9(
                                v___y_8126_,
                                v___x_8130_,
                                v_a_8096_,
                                v_a_8097_,
                                v_a_8098_,
                                v_a_8099_,
                                v_a_8100_,
                                v_a_8101_,
                                v_a_8102_,
                                leanh::lean_box(0),
                            );
                            v___y_8112_ = v___y_8125_;
                            v___y_8113_ = v___x_8131_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___y_8126_);
                            v___y_8105_ = v___y_8125_;
                            v_a_8106_ = v_e_8094_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_8126_);
                        leanh::lean_dec_ref(v___y_8125_);
                        leanh::lean_dec_ref(v_e_8094_);
                        v_a_8132_ = leanh::lean_ctor_get(v___x_8127_, 0);
                        v_isSharedCheck_8139_ =
                            (!leanh::lean_is_exclusive(v___x_8127_)) as u8;
                        if v_isSharedCheck_8139_ == 0 {
                            v___x_8134_ = v___x_8127_;
                            v_isShared_8135_ = v_isSharedCheck_8139_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8132_);
                            leanh::lean_dec(v___x_8127_);
                            v___x_8134_ = leanh::lean_box(0);
                            v_isShared_8135_ = v_isSharedCheck_8139_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_8094_);
                    v___x_8140_ = leanh::lean_box(0);
                    leanh::lean_inc(v_a_8102_);
                    leanh::lean_inc_ref(v_a_8101_);
                    leanh::lean_inc(v_a_8100_);
                    leanh::lean_inc_ref(v_a_8099_);
                    leanh::lean_inc(v_a_8098_);
                    leanh::lean_inc(v_a_8097_);
                    leanh::lean_inc_ref(v_a_8096_);
                    v___x_8141_ = leanh::lean_apply_9(
                        v___y_8126_,
                        v___x_8140_,
                        v_a_8096_,
                        v_a_8097_,
                        v_a_8098_,
                        v_a_8099_,
                        v_a_8100_,
                        v_a_8101_,
                        v_a_8102_,
                        leanh::lean_box(0),
                    );
                    v___y_8112_ = v___y_8125_;
                    v___y_8113_ = v___x_8141_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_8135_ == 0 {
                    v___x_8137_ = v___x_8134_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8138_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8138_, 0, v_a_8132_);
                    v___x_8137_ = v_reuseFailAlloc_8138_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8137_;
            }
            7 => {
                v___x_8144_ = lean_st_ref_get(v_a_8097_);
                v___x_8145_ = leanh::lean_box((v_topLevel_8095_) as usize);
                leanh::lean_inc_ref(v_e_8094_);
                v___x_8146_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8146_, 0, v___x_8145_);
                leanh::lean_ctor_set(v___x_8146_, 1, v_e_8094_);
                v___x_8147_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v___x_8144_, v___x_8146_);
                leanh::lean_dec(v___x_8144_);
                if leanh::lean_obj_tag(v___x_8147_) == 0 {
                    v___x_8148_ = l_Lean_Meta_ExtractLets_containsLet(v_e_8094_);
                    if v___x_8148_ == 0 {
                        leanh::lean_dec(v_fvars_8093_);
                        v___y_8105_ = v___x_8146_;
                        v_a_8106_ = v_e_8094_;
                        state = 1;
                        continue;
                    } else {
                        v___x_8149_ = leanh::lean_box((v_descend_8123_) as usize);
                        v___x_8150_ = leanh::lean_box((v___x_8148_) as usize);
                        v___x_8151_ = leanh::lean_box((v_topLevel_8095_) as usize);
                        v___x_8152_ = leanh::lean_box((v___y_8143_) as usize);
                        leanh::lean_inc_ref_n(v_e_8094_, 2);
                        v___f_8153_ = leanh::lean_alloc_closure(
                            l_Lean_Meta_ExtractLets_extractCore___lam__3___boxed
                                as *mut core::ffi::c_void,
                            15,
                            6,
                        );
                        leanh::lean_closure_set(v___f_8153_, 0, v___x_8149_);
                        leanh::lean_closure_set(v___f_8153_, 1, v_e_8094_);
                        leanh::lean_closure_set(v___f_8153_, 2, v_fvars_8093_);
                        leanh::lean_closure_set(v___f_8153_, 3, v___x_8150_);
                        leanh::lean_closure_set(v___f_8153_, 4, v___x_8151_);
                        leanh::lean_closure_set(v___f_8153_, 5, v___x_8152_);
                        v___x_8154_ = leanh::lean_box((v_types_8122_) as usize);
                        leanh::lean_inc_ref(v___f_8153_);
                        v___f_8155_ = leanh::lean_alloc_closure(
                            l_Lean_Meta_ExtractLets_extractCore___lam__4___boxed
                                as *mut core::ffi::c_void,
                            12,
                            3,
                        );
                        leanh::lean_closure_set(v___f_8155_, 0, v___x_8154_);
                        leanh::lean_closure_set(v___f_8155_, 1, v_e_8094_);
                        leanh::lean_closure_set(v___f_8155_, 2, v___f_8153_);
                        if v_topLevel_8095_ == 0 {
                            leanh::lean_dec_ref(v___f_8153_);
                            v___y_8125_ = v___x_8146_;
                            v___y_8126_ = v___f_8155_;
                            state = 4;
                            continue;
                        } else {
                            v___x_8156_ = l_Lean_Expr_isLet(v_e_8094_);
                            if v___x_8156_ == 0 {
                                v___x_8157_ = l_Lean_Expr_isMData(v_e_8094_);
                                if v___x_8157_ == 0 {
                                    leanh::lean_dec_ref(v___f_8153_);
                                    v___y_8125_ = v___x_8146_;
                                    v___y_8126_ = v___f_8155_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v___f_8155_);
                                    leanh::lean_dec_ref(v_e_8094_);
                                    v___y_8116_ = v___x_8146_;
                                    v___y_8117_ = v___f_8153_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v___f_8155_);
                                leanh::lean_dec_ref(v_e_8094_);
                                v___y_8116_ = v___x_8146_;
                                v___y_8117_ = v___f_8153_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_8146_, 2);
                    leanh::lean_dec_ref(v_e_8094_);
                    leanh::lean_dec(v_fvars_8093_);
                    v_val_8158_ = leanh::lean_ctor_get(v___x_8147_, 0);
                    v_isSharedCheck_8165_ = (!leanh::lean_is_exclusive(v___x_8147_)) as u8;
                    if v_isSharedCheck_8165_ == 0 {
                        v___x_8160_ = v___x_8147_;
                        v_isShared_8161_ = v_isSharedCheck_8165_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_8158_);
                        leanh::lean_dec(v___x_8147_);
                        v___x_8160_ = leanh::lean_box(0);
                        v_isShared_8161_ = v_isSharedCheck_8165_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_8161_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_8160_, 0);
                    v___x_8163_ = v___x_8160_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8164_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8164_, 0, v_val_8158_);
                    v___x_8163_ = v_reuseFailAlloc_8164_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8163_;
            }
            10 => {
                if v_topLevel_8095_ == 0 {
                    leanh::lean_dec(v_fvars_8093_);
                    v___x_8167_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8167_, 0, v_e_8094_);
                    return v___x_8167_;
                } else {
                    if v___x_8120_ == 0 {
                        v___y_8143_ = v___x_8120_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec(v_fvars_8093_);
                        v___x_8168_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_8168_, 0, v_e_8094_);
                        return v___x_8168_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_extractCore___lam__2(
    mut v_fvars_8170_: *mut leanh::LeanObject,
    mut v_struct_8171_: *mut leanh::LeanObject,
    mut v___y_8172_: u8,
    mut v_typeName_8173_: *mut leanh::LeanObject,
    mut v_idx_8174_: *mut leanh::LeanObject,
    mut v_e_8175_: *mut leanh::LeanObject,
    mut v___y_8176_: *mut leanh::LeanObject,
    mut v___y_8177_: *mut leanh::LeanObject,
    mut v___y_8178_: *mut leanh::LeanObject,
    mut v___y_8179_: *mut leanh::LeanObject,
    mut v___y_8180_: *mut leanh::LeanObject,
    mut v___y_8181_: *mut leanh::LeanObject,
    mut v___y_8182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8188_: u8 = 0;
    let mut v___x_8189_: usize = 0;
    let mut v___x_8190_: usize = 0;
    let mut v___x_8191_: u8 = 0;
    let mut v___x_8192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_struct_8171_);
                v___x_8184_ = l_Lean_Meta_ExtractLets_extractCore(
                    v_fvars_8170_,
                    v_struct_8171_,
                    v___y_8172_,
                    v___y_8176_,
                    v___y_8177_,
                    v___y_8178_,
                    v___y_8179_,
                    v___y_8180_,
                    v___y_8181_,
                    v___y_8182_,
                );
                if leanh::lean_obj_tag(v___x_8184_) == 0 {
                    v_a_8185_ = leanh::lean_ctor_get(v___x_8184_, 0);
                    v_isSharedCheck_8199_ = (!leanh::lean_is_exclusive(v___x_8184_)) as u8;
                    if v_isSharedCheck_8199_ == 0 {
                        v___x_8187_ = v___x_8184_;
                        v_isShared_8188_ = v_isSharedCheck_8199_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8185_);
                        leanh::lean_dec(v___x_8184_);
                        v___x_8187_ = leanh::lean_box(0);
                        v_isShared_8188_ = v_isSharedCheck_8199_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_8175_);
                    leanh::lean_dec(v_idx_8174_);
                    leanh::lean_dec(v_typeName_8173_);
                    leanh::lean_dec_ref(v_struct_8171_);
                    return v___x_8184_;
                }
            }
            1 => {
                v___x_8189_ = lean_ptr_addr(v_struct_8171_);
                leanh::lean_dec_ref(v_struct_8171_);
                v___x_8190_ = lean_ptr_addr(v_a_8185_);
                v___x_8191_ = lean_usize_dec_eq(v___x_8189_, v___x_8190_);
                if v___x_8191_ == 0 {
                    leanh::lean_dec_ref(v_e_8175_);
                    v___x_8192_ =
                        l_Lean_Expr_proj___override(v_typeName_8173_, v_idx_8174_, v_a_8185_);
                    if v_isShared_8188_ == 0 {
                        leanh::lean_ctor_set(v___x_8187_, 0, v___x_8192_);
                        v___x_8194_ = v___x_8187_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8195_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8195_, 0, v___x_8192_);
                        v___x_8194_ = v_reuseFailAlloc_8195_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_8185_);
                    leanh::lean_dec(v_idx_8174_);
                    leanh::lean_dec(v_typeName_8173_);
                    if v_isShared_8188_ == 0 {
                        leanh::lean_ctor_set(v___x_8187_, 0, v_e_8175_);
                        v___x_8197_ = v___x_8187_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8198_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8198_, 0, v_e_8175_);
                        v___x_8197_ = v_reuseFailAlloc_8198_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_8194_;
            }
            3 => {
                return v___x_8197_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7___boxed(
    mut v_fvars_8200_: *mut leanh::LeanObject,
    mut v_sz_8201_: *mut leanh::LeanObject,
    mut v_i_8202_: *mut leanh::LeanObject,
    mut v_bs_8203_: *mut leanh::LeanObject,
    mut v___y_8204_: *mut leanh::LeanObject,
    mut v___y_8205_: *mut leanh::LeanObject,
    mut v___y_8206_: *mut leanh::LeanObject,
    mut v___y_8207_: *mut leanh::LeanObject,
    mut v___y_8208_: *mut leanh::LeanObject,
    mut v___y_8209_: *mut leanh::LeanObject,
    mut v___y_8210_: *mut leanh::LeanObject,
    mut v___y_8211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_8212_: usize = 0;
    let mut v_i_boxed_8213_: usize = 0;
    let mut v_res_8214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8212_ = leanh::lean_unbox_usize(v_sz_8201_);
    leanh::lean_dec(v_sz_8201_);
    v_i_boxed_8213_ = leanh::lean_unbox_usize(v_i_8202_);
    leanh::lean_dec(v_i_8202_);
    v_res_8214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__7(v_fvars_8200_, v_sz_boxed_8212_, v_i_boxed_8213_, v_bs_8203_, v___y_8204_, v___y_8205_, v___y_8206_, v___y_8207_, v___y_8208_, v___y_8209_, v___y_8210_);
    leanh::lean_dec(v___y_8210_);
    leanh::lean_dec_ref(v___y_8209_);
    leanh::lean_dec(v___y_8208_);
    leanh::lean_dec_ref(v___y_8207_);
    leanh::lean_dec(v___y_8206_);
    leanh::lean_dec(v___y_8205_);
    leanh::lean_dec_ref(v___y_8204_);
    return v_res_8214_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg___boxed(
    mut v_upperBound_8215_: *mut leanh::LeanObject,
    mut v_fst_8216_: *mut leanh::LeanObject,
    mut v_fvars_8217_: *mut leanh::LeanObject,
    mut v_a_8218_: *mut leanh::LeanObject,
    mut v_b_8219_: *mut leanh::LeanObject,
    mut v___y_8220_: *mut leanh::LeanObject,
    mut v___y_8221_: *mut leanh::LeanObject,
    mut v___y_8222_: *mut leanh::LeanObject,
    mut v___y_8223_: *mut leanh::LeanObject,
    mut v___y_8224_: *mut leanh::LeanObject,
    mut v___y_8225_: *mut leanh::LeanObject,
    mut v___y_8226_: *mut leanh::LeanObject,
    mut v___y_8227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8228_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_8215_, v_fst_8216_, v_fvars_8217_, v_a_8218_, v_b_8219_, v___y_8220_, v___y_8221_, v___y_8222_, v___y_8223_, v___y_8224_, v___y_8225_, v___y_8226_);
    leanh::lean_dec(v___y_8226_);
    leanh::lean_dec_ref(v___y_8225_);
    leanh::lean_dec(v___y_8224_);
    leanh::lean_dec_ref(v___y_8223_);
    leanh::lean_dec(v___y_8222_);
    leanh::lean_dec(v___y_8221_);
    leanh::lean_dec_ref(v___y_8220_);
    leanh::lean_dec_ref(v_fst_8216_);
    leanh::lean_dec(v_upperBound_8215_);
    return v_res_8228_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike___boxed(
    mut v_fvars_8229_: *mut leanh::LeanObject,
    mut v_e_8230_: *mut leanh::LeanObject,
    mut v_isLet_8231_: *mut leanh::LeanObject,
    mut v_n_8232_: *mut leanh::LeanObject,
    mut v_t_8233_: *mut leanh::LeanObject,
    mut v_v_8234_: *mut leanh::LeanObject,
    mut v_b_8235_: *mut leanh::LeanObject,
    mut v_topLevel_8236_: *mut leanh::LeanObject,
    mut v_a_8237_: *mut leanh::LeanObject,
    mut v_a_8238_: *mut leanh::LeanObject,
    mut v_a_8239_: *mut leanh::LeanObject,
    mut v_a_8240_: *mut leanh::LeanObject,
    mut v_a_8241_: *mut leanh::LeanObject,
    mut v_a_8242_: *mut leanh::LeanObject,
    mut v_a_8243_: *mut leanh::LeanObject,
    mut v_a_8244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isLet_boxed_8245_: u8 = 0;
    let mut v_topLevel_boxed_8246_: u8 = 0;
    let mut v_res_8247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLet_boxed_8245_ = (leanh::lean_unbox(v_isLet_8231_) as u8);
    v_topLevel_boxed_8246_ = (leanh::lean_unbox(v_topLevel_8236_) as u8);
    v_res_8247_ =
        l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike(
            v_fvars_8229_,
            v_e_8230_,
            v_isLet_boxed_8245_,
            v_n_8232_,
            v_t_8233_,
            v_v_8234_,
            v_b_8235_,
            v_topLevel_boxed_8246_,
            v_a_8237_,
            v_a_8238_,
            v_a_8239_,
            v_a_8240_,
            v_a_8241_,
            v_a_8242_,
            v_a_8243_,
        );
    leanh::lean_dec(v_a_8243_);
    leanh::lean_dec_ref(v_a_8242_);
    leanh::lean_dec(v_a_8241_);
    leanh::lean_dec_ref(v_a_8240_);
    leanh::lean_dec(v_a_8239_);
    leanh::lean_dec(v_a_8238_);
    leanh::lean_dec_ref(v_a_8237_);
    return v_res_8247_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(
    mut v_00_u03b1_8248_: *mut leanh::LeanObject,
    mut v_name_8249_: *mut leanh::LeanObject,
    mut v_type_8250_: *mut leanh::LeanObject,
    mut v_val_8251_: *mut leanh::LeanObject,
    mut v_k_8252_: *mut leanh::LeanObject,
    mut v_nondep_8253_: u8,
    mut v_kind_8254_: u8,
    mut v___y_8255_: *mut leanh::LeanObject,
    mut v___y_8256_: *mut leanh::LeanObject,
    mut v___y_8257_: *mut leanh::LeanObject,
    mut v___y_8258_: *mut leanh::LeanObject,
    mut v___y_8259_: *mut leanh::LeanObject,
    mut v___y_8260_: *mut leanh::LeanObject,
    mut v___y_8261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8263_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___redArg(v_name_8249_, v_type_8250_, v_val_8251_, v_k_8252_, v_nondep_8253_, v_kind_8254_, v___y_8255_, v___y_8256_, v___y_8257_, v___y_8258_, v___y_8259_, v___y_8260_, v___y_8261_);
    return v___x_8263_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10___boxed(
    mut v_00_u03b1_8264_: *mut leanh::LeanObject,
    mut v_name_8265_: *mut leanh::LeanObject,
    mut v_type_8266_: *mut leanh::LeanObject,
    mut v_val_8267_: *mut leanh::LeanObject,
    mut v_k_8268_: *mut leanh::LeanObject,
    mut v_nondep_8269_: *mut leanh::LeanObject,
    mut v_kind_8270_: *mut leanh::LeanObject,
    mut v___y_8271_: *mut leanh::LeanObject,
    mut v___y_8272_: *mut leanh::LeanObject,
    mut v___y_8273_: *mut leanh::LeanObject,
    mut v___y_8274_: *mut leanh::LeanObject,
    mut v___y_8275_: *mut leanh::LeanObject,
    mut v___y_8276_: *mut leanh::LeanObject,
    mut v___y_8277_: *mut leanh::LeanObject,
    mut v___y_8278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_boxed_8279_: u8 = 0;
    let mut v_kind_boxed_8280_: u8 = 0;
    let mut v_res_8281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_8279_ = (leanh::lean_unbox(v_nondep_8269_) as u8);
    v_kind_boxed_8280_ = (leanh::lean_unbox(v_kind_8270_) as u8);
    v_res_8281_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__10(v_00_u03b1_8264_, v_name_8265_, v_type_8266_, v_val_8267_, v_k_8268_, v_nondep_boxed_8279_, v_kind_boxed_8280_, v___y_8271_, v___y_8272_, v___y_8273_, v___y_8274_, v___y_8275_, v___y_8276_, v___y_8277_);
    leanh::lean_dec(v___y_8277_);
    leanh::lean_dec_ref(v___y_8276_);
    leanh::lean_dec(v___y_8275_);
    leanh::lean_dec_ref(v___y_8274_);
    leanh::lean_dec(v___y_8273_);
    leanh::lean_dec(v___y_8272_);
    leanh::lean_dec_ref(v___y_8271_);
    return v_res_8281_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2(
    mut v_00_u03b2_8282_: *mut leanh::LeanObject,
    mut v_m_8283_: *mut leanh::LeanObject,
    mut v_a_8284_: *mut leanh::LeanObject,
    mut v_b_8285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8286_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2___redArg(v_m_8283_, v_a_8284_, v_b_8285_);
    return v___x_8286_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(
    mut v_00_u03b2_8287_: *mut leanh::LeanObject,
    mut v_m_8288_: *mut leanh::LeanObject,
    mut v_a_8289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8290_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___redArg(v_m_8288_, v_a_8289_);
    return v___x_8290_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3___boxed(
    mut v_00_u03b2_8291_: *mut leanh::LeanObject,
    mut v_m_8292_: *mut leanh::LeanObject,
    mut v_a_8293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3(v_00_u03b2_8291_, v_m_8292_, v_a_8293_);
    leanh::lean_dec_ref(v_a_8293_);
    leanh::lean_dec_ref(v_m_8292_);
    return v_res_8294_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(
    mut v_upperBound_8295_: *mut leanh::LeanObject,
    mut v_fst_8296_: *mut leanh::LeanObject,
    mut v_fvars_8297_: *mut leanh::LeanObject,
    mut v_inst_8298_: *mut leanh::LeanObject,
    mut v_R_8299_: *mut leanh::LeanObject,
    mut v_a_8300_: *mut leanh::LeanObject,
    mut v_b_8301_: *mut leanh::LeanObject,
    mut v_c_8302_: *mut leanh::LeanObject,
    mut v___y_8303_: *mut leanh::LeanObject,
    mut v___y_8304_: *mut leanh::LeanObject,
    mut v___y_8305_: *mut leanh::LeanObject,
    mut v___y_8306_: *mut leanh::LeanObject,
    mut v___y_8307_: *mut leanh::LeanObject,
    mut v___y_8308_: *mut leanh::LeanObject,
    mut v___y_8309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8311_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___redArg(v_upperBound_8295_, v_fst_8296_, v_fvars_8297_, v_a_8300_, v_b_8301_, v___y_8303_, v___y_8304_, v___y_8305_, v___y_8306_, v___y_8307_, v___y_8308_, v___y_8309_);
    return v___x_8311_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6___boxed(
    mut v_upperBound_8312_: *mut leanh::LeanObject,
    mut v_fst_8313_: *mut leanh::LeanObject,
    mut v_fvars_8314_: *mut leanh::LeanObject,
    mut v_inst_8315_: *mut leanh::LeanObject,
    mut v_R_8316_: *mut leanh::LeanObject,
    mut v_a_8317_: *mut leanh::LeanObject,
    mut v_b_8318_: *mut leanh::LeanObject,
    mut v_c_8319_: *mut leanh::LeanObject,
    mut v___y_8320_: *mut leanh::LeanObject,
    mut v___y_8321_: *mut leanh::LeanObject,
    mut v___y_8322_: *mut leanh::LeanObject,
    mut v___y_8323_: *mut leanh::LeanObject,
    mut v___y_8324_: *mut leanh::LeanObject,
    mut v___y_8325_: *mut leanh::LeanObject,
    mut v___y_8326_: *mut leanh::LeanObject,
    mut v___y_8327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8328_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractApp_spec__6(v_upperBound_8312_, v_fst_8313_, v_fvars_8314_, v_inst_8315_, v_R_8316_, v_a_8317_, v_b_8318_, v_c_8319_, v___y_8320_, v___y_8321_, v___y_8322_, v___y_8323_, v___y_8324_, v___y_8325_, v___y_8326_);
    leanh::lean_dec(v___y_8326_);
    leanh::lean_dec_ref(v___y_8325_);
    leanh::lean_dec(v___y_8324_);
    leanh::lean_dec_ref(v___y_8323_);
    leanh::lean_dec(v___y_8322_);
    leanh::lean_dec(v___y_8321_);
    leanh::lean_dec_ref(v___y_8320_);
    leanh::lean_dec_ref(v_fst_8313_);
    leanh::lean_dec(v_upperBound_8312_);
    return v_res_8328_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(
    mut v_00_u03b2_8329_: *mut leanh::LeanObject,
    mut v_m_8330_: *mut leanh::LeanObject,
    mut v_a_8331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8332_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___redArg(v_m_8330_, v_a_8331_);
    return v___x_8332_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11___boxed(
    mut v_00_u03b2_8333_: *mut leanh::LeanObject,
    mut v_m_8334_: *mut leanh::LeanObject,
    mut v_a_8335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8336_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11(v_00_u03b2_8333_, v_m_8334_, v_a_8335_);
    leanh::lean_dec_ref(v_a_8335_);
    leanh::lean_dec_ref(v_m_8334_);
    return v_res_8336_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(
    mut v_00_u03b2_8337_: *mut leanh::LeanObject,
    mut v_a_8338_: *mut leanh::LeanObject,
    mut v_x_8339_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_8340_: u8 = 0;
    v___x_8340_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___redArg(v_a_8338_, v_x_8339_);
    return v___x_8340_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2___boxed(
    mut v_00_u03b2_8341_: *mut leanh::LeanObject,
    mut v_a_8342_: *mut leanh::LeanObject,
    mut v_x_8343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8344_: u8 = 0;
    let mut v_r_8345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8344_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__2(v_00_u03b2_8341_, v_a_8342_, v_x_8343_);
    leanh::lean_dec(v_x_8343_);
    leanh::lean_dec_ref(v_a_8342_);
    v_r_8345_ = leanh::lean_box((v_res_8344_) as usize);
    return v_r_8345_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3(
    mut v_00_u03b2_8346_: *mut leanh::LeanObject,
    mut v_data_8347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8348_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3___redArg(v_data_8347_);
    return v___x_8348_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4(
    mut v_00_u03b2_8349_: *mut leanh::LeanObject,
    mut v_a_8350_: *mut leanh::LeanObject,
    mut v_b_8351_: *mut leanh::LeanObject,
    mut v_x_8352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8353_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__4___redArg(v_a_8350_, v_b_8351_, v_x_8352_);
    return v___x_8353_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(
    mut v_00_u03b2_8354_: *mut leanh::LeanObject,
    mut v_a_8355_: *mut leanh::LeanObject,
    mut v_x_8356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8357_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___redArg(v_a_8355_, v_x_8356_);
    return v___x_8357_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6___boxed(
    mut v_00_u03b2_8358_: *mut leanh::LeanObject,
    mut v_a_8359_: *mut leanh::LeanObject,
    mut v_x_8360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8361_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_ExtractLets_extractCore_spec__3_spec__6(v_00_u03b2_8358_, v_a_8359_, v_x_8360_);
    leanh::lean_dec(v_x_8360_);
    leanh::lean_dec_ref(v_a_8359_);
    return v_res_8361_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(
    mut v_00_u03b2_8362_: *mut leanh::LeanObject,
    mut v_a_8363_: *mut leanh::LeanObject,
    mut v_x_8364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8365_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___redArg(v_a_8363_, v_x_8364_);
    return v___x_8365_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15___boxed(
    mut v_00_u03b2_8366_: *mut leanh::LeanObject,
    mut v_a_8367_: *mut leanh::LeanObject,
    mut v_x_8368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8369_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_ExtractLets_extractCore_extractLetLike_spec__11_spec__15(v_00_u03b2_8366_, v_a_8367_, v_x_8368_);
    leanh::lean_dec(v_x_8368_);
    leanh::lean_dec_ref(v_a_8367_);
    return v_res_8369_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9(
    mut v_00_u03b2_8370_: *mut leanh::LeanObject,
    mut v_i_8371_: *mut leanh::LeanObject,
    mut v_source_8372_: *mut leanh::LeanObject,
    mut v_target_8373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8374_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9___redArg(v_i_8371_, v_source_8372_, v_target_8373_);
    return v___x_8374_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14(
    mut v_00_u03b2_8375_: *mut leanh::LeanObject,
    mut v_x_8376_: *mut leanh::LeanObject,
    mut v_x_8377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8378_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_ExtractLets_extractCore_spec__2_spec__3_spec__9_spec__14___redArg(v_x_8376_, v_x_8377_);
    return v___x_8378_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_extractTopLevel(
    mut v_e_8379_: *mut leanh::LeanObject,
    mut v_a_8380_: *mut leanh::LeanObject,
    mut v_a_8381_: *mut leanh::LeanObject,
    mut v_a_8382_: *mut leanh::LeanObject,
    mut v_a_8383_: *mut leanh::LeanObject,
    mut v_a_8384_: *mut leanh::LeanObject,
    mut v_a_8385_: *mut leanh::LeanObject,
    mut v_a_8386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8391_: u8 = 0;
    let mut v___x_8392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8388_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_ExtractLets_initializeValueMap_spec__0___redArg(
            v_e_8379_, v_a_8384_,
        );
    v_a_8389_ = leanh::lean_ctor_get(v___x_8388_, 0);
    leanh::lean_inc(v_a_8389_);
    leanh::lean_dec_ref(v___x_8388_);
    v___x_8390_ = leanh::lean_box(0);
    v___x_8391_ = 1;
    v___x_8392_ = l_Lean_Meta_ExtractLets_extractCore(
        v___x_8390_,
        v_a_8389_,
        v___x_8391_,
        v_a_8380_,
        v_a_8381_,
        v_a_8382_,
        v_a_8383_,
        v_a_8384_,
        v_a_8385_,
        v_a_8386_,
    );
    return v___x_8392_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_extractTopLevel___boxed(
    mut v_e_8393_: *mut leanh::LeanObject,
    mut v_a_8394_: *mut leanh::LeanObject,
    mut v_a_8395_: *mut leanh::LeanObject,
    mut v_a_8396_: *mut leanh::LeanObject,
    mut v_a_8397_: *mut leanh::LeanObject,
    mut v_a_8398_: *mut leanh::LeanObject,
    mut v_a_8399_: *mut leanh::LeanObject,
    mut v_a_8400_: *mut leanh::LeanObject,
    mut v_a_8401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8402_ = l_Lean_Meta_ExtractLets_extractTopLevel(
        v_e_8393_, v_a_8394_, v_a_8395_, v_a_8396_, v_a_8397_, v_a_8398_, v_a_8399_, v_a_8400_,
    );
    leanh::lean_dec(v_a_8400_);
    leanh::lean_dec_ref(v_a_8399_);
    leanh::lean_dec(v_a_8398_);
    leanh::lean_dec_ref(v_a_8397_);
    leanh::lean_dec(v_a_8396_);
    leanh::lean_dec(v_a_8395_);
    leanh::lean_dec_ref(v_a_8394_);
    return v_res_8402_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(
    mut v_sz_8403_: usize,
    mut v_i_8404_: usize,
    mut v_bs_8405_: *mut leanh::LeanObject,
    mut v___y_8406_: *mut leanh::LeanObject,
    mut v___y_8407_: *mut leanh::LeanObject,
    mut v___y_8408_: *mut leanh::LeanObject,
    mut v___y_8409_: *mut leanh::LeanObject,
    mut v___y_8410_: *mut leanh::LeanObject,
    mut v___y_8411_: *mut leanh::LeanObject,
    mut v___y_8412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8414_: u8 = 0;
    let mut v___x_8415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_8420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8421_: usize = 0;
    let mut v___x_8422_: usize = 0;
    let mut v___x_8423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8428_: u8 = 0;
    let mut v___x_8430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8432_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8414_ = lean_usize_dec_lt(v_i_8404_, v_sz_8403_);
                if v___x_8414_ == 0 {
                    v___x_8415_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8415_, 0, v_bs_8405_);
                    return v___x_8415_;
                } else {
                    v_v_8416_ = lean_array_uget_borrowed(v_bs_8405_, v_i_8404_);
                    leanh::lean_inc(v_v_8416_);
                    v___x_8417_ = l_Lean_Meta_ExtractLets_extractTopLevel(
                        v_v_8416_,
                        v___y_8406_,
                        v___y_8407_,
                        v___y_8408_,
                        v___y_8409_,
                        v___y_8410_,
                        v___y_8411_,
                        v___y_8412_,
                    );
                    if leanh::lean_obj_tag(v___x_8417_) == 0 {
                        v_a_8418_ = leanh::lean_ctor_get(v___x_8417_, 0);
                        leanh::lean_inc(v_a_8418_);
                        leanh::lean_dec_ref_known(v___x_8417_, 1);
                        v___x_8419_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_8420_ = lean_array_uset(v_bs_8405_, v_i_8404_, v___x_8419_);
                        v___x_8421_ = 1usize;
                        v___x_8422_ = lean_usize_add(v_i_8404_, v___x_8421_);
                        v___x_8423_ = lean_array_uset(v_bs_x27_8420_, v_i_8404_, v_a_8418_);
                        v_i_8404_ = v___x_8422_;
                        v_bs_8405_ = v___x_8423_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_8405_);
                        v_a_8425_ = leanh::lean_ctor_get(v___x_8417_, 0);
                        v_isSharedCheck_8432_ =
                            (!leanh::lean_is_exclusive(v___x_8417_)) as u8;
                        if v_isSharedCheck_8432_ == 0 {
                            v___x_8427_ = v___x_8417_;
                            v_isShared_8428_ = v_isSharedCheck_8432_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8425_);
                            leanh::lean_dec(v___x_8417_);
                            v___x_8427_ = leanh::lean_box(0);
                            v_isShared_8428_ = v_isSharedCheck_8432_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_8428_ == 0 {
                    v___x_8430_ = v___x_8427_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8431_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8431_, 0, v_a_8425_);
                    v___x_8430_ = v_reuseFailAlloc_8431_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8430_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0___boxed(
    mut v_sz_8433_: *mut leanh::LeanObject,
    mut v_i_8434_: *mut leanh::LeanObject,
    mut v_bs_8435_: *mut leanh::LeanObject,
    mut v___y_8436_: *mut leanh::LeanObject,
    mut v___y_8437_: *mut leanh::LeanObject,
    mut v___y_8438_: *mut leanh::LeanObject,
    mut v___y_8439_: *mut leanh::LeanObject,
    mut v___y_8440_: *mut leanh::LeanObject,
    mut v___y_8441_: *mut leanh::LeanObject,
    mut v___y_8442_: *mut leanh::LeanObject,
    mut v___y_8443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_8444_: usize = 0;
    let mut v_i_boxed_8445_: usize = 0;
    let mut v_res_8446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8444_ = leanh::lean_unbox_usize(v_sz_8433_);
    leanh::lean_dec(v_sz_8433_);
    v_i_boxed_8445_ = leanh::lean_unbox_usize(v_i_8434_);
    leanh::lean_dec(v_i_8434_);
    v_res_8446_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_boxed_8444_, v_i_boxed_8445_, v_bs_8435_, v___y_8436_, v___y_8437_, v___y_8438_, v___y_8439_, v___y_8440_, v___y_8441_, v___y_8442_);
    leanh::lean_dec(v___y_8442_);
    leanh::lean_dec_ref(v___y_8441_);
    leanh::lean_dec(v___y_8440_);
    leanh::lean_dec_ref(v___y_8439_);
    leanh::lean_dec(v___y_8438_);
    leanh::lean_dec(v___y_8437_);
    leanh::lean_dec_ref(v___y_8436_);
    return v_res_8446_;
}
pub unsafe fn l_Lean_Meta_ExtractLets_extract(
    mut v_es_8447_: *mut leanh::LeanObject,
    mut v_a_8448_: *mut leanh::LeanObject,
    mut v_a_8449_: *mut leanh::LeanObject,
    mut v_a_8450_: *mut leanh::LeanObject,
    mut v_a_8451_: *mut leanh::LeanObject,
    mut v_a_8452_: *mut leanh::LeanObject,
    mut v_a_8453_: *mut leanh::LeanObject,
    mut v_a_8454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_8457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8464_: usize = 0;
    let mut v___x_8465_: usize = 0;
    let mut v___x_8466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_merge_8467_: u8 = 0;
    let mut v_useContext_8468_: u8 = 0;
    let mut v___x_8469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8473_: u8 = 0;
    let mut v___x_8475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8477_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_merge_8467_ = leanh::lean_ctor_get_uint8(v_a_8448_, 6 as u32);
                if v_merge_8467_ == 0 {
                    v___y_8457_ = v_a_8448_;
                    v___y_8458_ = v_a_8449_;
                    v___y_8459_ = v_a_8450_;
                    v___y_8460_ = v_a_8451_;
                    v___y_8461_ = v_a_8452_;
                    v___y_8462_ = v_a_8453_;
                    v___y_8463_ = v_a_8454_;
                    state = 1;
                    continue;
                } else {
                    v_useContext_8468_ = leanh::lean_ctor_get_uint8(v_a_8448_, 7 as u32);
                    if v_useContext_8468_ == 0 {
                        v___y_8457_ = v_a_8448_;
                        v___y_8458_ = v_a_8449_;
                        v___y_8459_ = v_a_8450_;
                        v___y_8460_ = v_a_8451_;
                        v___y_8461_ = v_a_8452_;
                        v___y_8462_ = v_a_8453_;
                        v___y_8463_ = v_a_8454_;
                        state = 1;
                        continue;
                    } else {
                        v___x_8469_ = l_Lean_Meta_ExtractLets_initializeValueMap(
                            v_a_8448_, v_a_8449_, v_a_8450_, v_a_8451_, v_a_8452_, v_a_8453_,
                            v_a_8454_,
                        );
                        if leanh::lean_obj_tag(v___x_8469_) == 0 {
                            leanh::lean_dec_ref_known(v___x_8469_, 1);
                            v___y_8457_ = v_a_8448_;
                            v___y_8458_ = v_a_8449_;
                            v___y_8459_ = v_a_8450_;
                            v___y_8460_ = v_a_8451_;
                            v___y_8461_ = v_a_8452_;
                            v___y_8462_ = v_a_8453_;
                            v___y_8463_ = v_a_8454_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_es_8447_);
                            v_a_8470_ = leanh::lean_ctor_get(v___x_8469_, 0);
                            v_isSharedCheck_8477_ =
                                (!leanh::lean_is_exclusive(v___x_8469_)) as u8;
                            if v_isSharedCheck_8477_ == 0 {
                                v___x_8472_ = v___x_8469_;
                                v_isShared_8473_ = v_isSharedCheck_8477_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_8470_);
                                leanh::lean_dec(v___x_8469_);
                                v___x_8472_ = leanh::lean_box(0);
                                v_isShared_8473_ = v_isSharedCheck_8477_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v_sz_8464_ = lean_array_size(v_es_8447_);
                v___x_8465_ = 0usize;
                v___x_8466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_extract_spec__0(v_sz_8464_, v___x_8465_, v_es_8447_, v___y_8457_, v___y_8458_, v___y_8459_, v___y_8460_, v___y_8461_, v___y_8462_, v___y_8463_);
                return v___x_8466_;
            }
            2 => {
                if v_isShared_8473_ == 0 {
                    v___x_8475_ = v___x_8472_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8476_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8476_, 0, v_a_8470_);
                    v___x_8475_ = v_reuseFailAlloc_8476_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8475_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ExtractLets_extract___boxed(
    mut v_es_8478_: *mut leanh::LeanObject,
    mut v_a_8479_: *mut leanh::LeanObject,
    mut v_a_8480_: *mut leanh::LeanObject,
    mut v_a_8481_: *mut leanh::LeanObject,
    mut v_a_8482_: *mut leanh::LeanObject,
    mut v_a_8483_: *mut leanh::LeanObject,
    mut v_a_8484_: *mut leanh::LeanObject,
    mut v_a_8485_: *mut leanh::LeanObject,
    mut v_a_8486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8487_ = l_Lean_Meta_ExtractLets_extract(
        v_es_8478_, v_a_8479_, v_a_8480_, v_a_8481_, v_a_8482_, v_a_8483_, v_a_8484_, v_a_8485_,
    );
    leanh::lean_dec(v_a_8485_);
    leanh::lean_dec_ref(v_a_8484_);
    leanh::lean_dec(v_a_8483_);
    leanh::lean_dec_ref(v_a_8482_);
    leanh::lean_dec(v_a_8481_);
    leanh::lean_dec(v_a_8480_);
    leanh::lean_dec_ref(v_a_8479_);
    return v_res_8487_;
}
pub unsafe fn l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(
    mut v_decls_8488_: *mut leanh::LeanObject,
    mut v_x_8489_: *mut leanh::LeanObject,
    mut v___y_8490_: *mut leanh::LeanObject,
    mut v___y_8491_: *mut leanh::LeanObject,
    mut v___y_8492_: *mut leanh::LeanObject,
    mut v___y_8493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8499_: u8 = 0;
    let mut v___x_8501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8503_: u8 = 0;
    let mut v_a_8504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8507_: u8 = 0;
    let mut v___x_8509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8511_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8495_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(
                    leanh::lean_box(0),
                    v_decls_8488_,
                    v_x_8489_,
                    v___y_8490_,
                    v___y_8491_,
                    v___y_8492_,
                    v___y_8493_,
                );
                if leanh::lean_obj_tag(v___x_8495_) == 0 {
                    v_a_8496_ = leanh::lean_ctor_get(v___x_8495_, 0);
                    v_isSharedCheck_8503_ = (!leanh::lean_is_exclusive(v___x_8495_)) as u8;
                    if v_isSharedCheck_8503_ == 0 {
                        v___x_8498_ = v___x_8495_;
                        v_isShared_8499_ = v_isSharedCheck_8503_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8496_);
                        leanh::lean_dec(v___x_8495_);
                        v___x_8498_ = leanh::lean_box(0);
                        v_isShared_8499_ = v_isSharedCheck_8503_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8504_ = leanh::lean_ctor_get(v___x_8495_, 0);
                    v_isSharedCheck_8511_ = (!leanh::lean_is_exclusive(v___x_8495_)) as u8;
                    if v_isSharedCheck_8511_ == 0 {
                        v___x_8506_ = v___x_8495_;
                        v_isShared_8507_ = v_isSharedCheck_8511_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8504_);
                        leanh::lean_dec(v___x_8495_);
                        v___x_8506_ = leanh::lean_box(0);
                        v_isShared_8507_ = v_isSharedCheck_8511_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8499_ == 0 {
                    v___x_8501_ = v___x_8498_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8502_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8502_, 0, v_a_8496_);
                    v___x_8501_ = v_reuseFailAlloc_8502_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8501_;
            }
            3 => {
                if v_isShared_8507_ == 0 {
                    v___x_8509_ = v___x_8506_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8510_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8510_, 0, v_a_8504_);
                    v___x_8509_ = v_reuseFailAlloc_8510_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8509_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg___boxed(
    mut v_decls_8512_: *mut leanh::LeanObject,
    mut v_x_8513_: *mut leanh::LeanObject,
    mut v___y_8514_: *mut leanh::LeanObject,
    mut v___y_8515_: *mut leanh::LeanObject,
    mut v___y_8516_: *mut leanh::LeanObject,
    mut v___y_8517_: *mut leanh::LeanObject,
    mut v___y_8518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8519_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_8512_, v_x_8513_, v___y_8514_, v___y_8515_, v___y_8516_, v___y_8517_);
    leanh::lean_dec(v___y_8517_);
    leanh::lean_dec_ref(v___y_8516_);
    leanh::lean_dec(v___y_8515_);
    leanh::lean_dec_ref(v___y_8514_);
    return v_res_8519_;
}
pub unsafe fn l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(
    mut v_00_u03b1_8520_: *mut leanh::LeanObject,
    mut v_decls_8521_: *mut leanh::LeanObject,
    mut v_x_8522_: *mut leanh::LeanObject,
    mut v___y_8523_: *mut leanh::LeanObject,
    mut v___y_8524_: *mut leanh::LeanObject,
    mut v___y_8525_: *mut leanh::LeanObject,
    mut v___y_8526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8528_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v_decls_8521_, v_x_8522_, v___y_8523_, v___y_8524_, v___y_8525_, v___y_8526_);
    return v___x_8528_;
}
pub unsafe fn l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___boxed(
    mut v_00_u03b1_8529_: *mut leanh::LeanObject,
    mut v_decls_8530_: *mut leanh::LeanObject,
    mut v_x_8531_: *mut leanh::LeanObject,
    mut v___y_8532_: *mut leanh::LeanObject,
    mut v___y_8533_: *mut leanh::LeanObject,
    mut v___y_8534_: *mut leanh::LeanObject,
    mut v___y_8535_: *mut leanh::LeanObject,
    mut v___y_8536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8537_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1(v_00_u03b1_8529_, v_decls_8530_, v_x_8531_, v___y_8532_, v___y_8533_, v___y_8534_, v___y_8535_);
    leanh::lean_dec(v___y_8535_);
    leanh::lean_dec_ref(v___y_8534_);
    leanh::lean_dec(v___y_8533_);
    leanh::lean_dec_ref(v___y_8532_);
    return v_res_8537_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(
    mut v_sz_8538_: usize,
    mut v_i_8539_: usize,
    mut v_bs_8540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8541_: u8 = 0;
    let mut v_v_8542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_8544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8546_: usize = 0;
    let mut v___x_8547_: usize = 0;
    let mut v___x_8548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8541_ = lean_usize_dec_lt(v_i_8539_, v_sz_8538_);
                if v___x_8541_ == 0 {
                    return v_bs_8540_;
                } else {
                    v_v_8542_ = lean_array_uget(v_bs_8540_, v_i_8539_);
                    v___x_8543_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_8544_ = lean_array_uset(v_bs_8540_, v_i_8539_, v___x_8543_);
                    v___x_8545_ = l_Lean_LocalDecl_fvarId(v_v_8542_);
                    leanh::lean_dec(v_v_8542_);
                    v___x_8546_ = 1usize;
                    v___x_8547_ = lean_usize_add(v_i_8539_, v___x_8546_);
                    v___x_8548_ = lean_array_uset(v_bs_x27_8544_, v_i_8539_, v___x_8545_);
                    v_i_8539_ = v___x_8547_;
                    v_bs_8540_ = v___x_8548_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0___boxed(
    mut v_sz_8550_: *mut leanh::LeanObject,
    mut v_i_8551_: *mut leanh::LeanObject,
    mut v_bs_8552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_8553_: usize = 0;
    let mut v_i_boxed_8554_: usize = 0;
    let mut v_res_8555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8553_ = leanh::lean_unbox_usize(v_sz_8550_);
    leanh::lean_dec(v_sz_8550_);
    v_i_boxed_8554_ = leanh::lean_unbox_usize(v_i_8551_);
    leanh::lean_dec(v_i_8551_);
    v_res_8555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_boxed_8553_, v_i_boxed_8554_, v_bs_8552_);
    return v_res_8555_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_8556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8556_ = leanh::lean_box(0);
    v___x_8557_ = leanh::lean_unsigned_to_nat(16);
    v___x_8558_ = lean_mk_array(v___x_8557_, v___x_8556_);
    return v___x_8558_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_8559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8559_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0_once
        ),
        _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__0,
    );
    v___x_8560_ = leanh::lean_unsigned_to_nat(0);
    v___x_8561_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_8561_, 0, v___x_8560_);
    leanh::lean_ctor_set(v___x_8561_, 1, v___x_8559_);
    return v___x_8561_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(
    mut v_es_8562_: *mut leanh::LeanObject,
    mut v_givenNames_8563_: *mut leanh::LeanObject,
    mut v_k_8564_: *mut leanh::LeanObject,
    mut v_config_8565_: *mut leanh::LeanObject,
    mut v_a_8566_: *mut leanh::LeanObject,
    mut v_a_8567_: *mut leanh::LeanObject,
    mut v_a_8568_: *mut leanh::LeanObject,
    mut v_a_8569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_givenNames_8580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_8581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8582_: usize = 0;
    let mut v___x_8583_: usize = 0;
    let mut v___x_8584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8586_: usize = 0;
    let mut v___x_8587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8593_: u8 = 0;
    let mut v___x_8595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8571_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
                v___x_8572_ = l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0;
                v___x_8573_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_8573_, 0, v_givenNames_8563_);
                leanh::lean_ctor_set(v___x_8573_, 1, v___x_8572_);
                leanh::lean_ctor_set(v___x_8573_, 2, v___x_8571_);
                v___x_8574_ = lean_st_mk_ref(v___x_8573_);
                v___x_8575_ = lean_st_mk_ref(v___x_8571_);
                v___x_8576_ = l_Lean_Meta_ExtractLets_extract(
                    v_es_8562_,
                    v_config_8565_,
                    v___x_8575_,
                    v___x_8574_,
                    v_a_8566_,
                    v_a_8567_,
                    v_a_8568_,
                    v_a_8569_,
                );
                if leanh::lean_obj_tag(v___x_8576_) == 0 {
                    v_a_8577_ = leanh::lean_ctor_get(v___x_8576_, 0);
                    leanh::lean_inc(v_a_8577_);
                    leanh::lean_dec_ref_known(v___x_8576_, 1);
                    v___x_8578_ = lean_st_ref_get(v___x_8575_);
                    leanh::lean_dec(v___x_8575_);
                    leanh::lean_dec(v___x_8578_);
                    v___x_8579_ = lean_st_ref_get(v___x_8574_);
                    leanh::lean_dec(v___x_8574_);
                    v_givenNames_8580_ = leanh::lean_ctor_get(v___x_8579_, 0);
                    leanh::lean_inc(v_givenNames_8580_);
                    v_decls_8581_ = leanh::lean_ctor_get(v___x_8579_, 1);
                    leanh::lean_inc_ref(v_decls_8581_);
                    leanh::lean_dec(v___x_8579_);
                    v_sz_8582_ = lean_array_size(v_decls_8581_);
                    v___x_8583_ = 0usize;
                    v___x_8584_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ExtractLets_withEnsuringDeclsInContext___at___00Lean_Meta_ExtractLets_withDeclInContext_spec__1_spec__1(v_sz_8582_, v___x_8583_, v_decls_8581_);
                    leanh::lean_inc_ref(v___x_8584_);
                    v___x_8585_ = lean_array_to_list(v___x_8584_);
                    v_sz_8586_ = lean_array_size(v___x_8584_);
                    v___x_8587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__0(v_sz_8586_, v___x_8583_, v___x_8584_);
                    v___x_8588_ = leanh::lean_apply_3(
                        v_k_8564_,
                        v___x_8587_,
                        v_a_8577_,
                        v_givenNames_8580_,
                    );
                    v___x_8589_ = l_Lean_Meta_withExistingLocalDecls___at___00__private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp_spec__1___redArg(v___x_8585_, v___x_8588_, v_a_8566_, v_a_8567_, v_a_8568_, v_a_8569_);
                    return v___x_8589_;
                } else {
                    leanh::lean_dec(v___x_8575_);
                    leanh::lean_dec(v___x_8574_);
                    leanh::lean_dec_ref(v_k_8564_);
                    v_a_8590_ = leanh::lean_ctor_get(v___x_8576_, 0);
                    v_isSharedCheck_8597_ = (!leanh::lean_is_exclusive(v___x_8576_)) as u8;
                    if v_isSharedCheck_8597_ == 0 {
                        v___x_8592_ = v___x_8576_;
                        v_isShared_8593_ = v_isSharedCheck_8597_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8590_);
                        leanh::lean_dec(v___x_8576_);
                        v___x_8592_ = leanh::lean_box(0);
                        v_isShared_8593_ = v_isSharedCheck_8597_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8593_ == 0 {
                    v___x_8595_ = v___x_8592_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8596_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8596_, 0, v_a_8590_);
                    v___x_8595_ = v_reuseFailAlloc_8596_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8595_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___boxed(
    mut v_es_8598_: *mut leanh::LeanObject,
    mut v_givenNames_8599_: *mut leanh::LeanObject,
    mut v_k_8600_: *mut leanh::LeanObject,
    mut v_config_8601_: *mut leanh::LeanObject,
    mut v_a_8602_: *mut leanh::LeanObject,
    mut v_a_8603_: *mut leanh::LeanObject,
    mut v_a_8604_: *mut leanh::LeanObject,
    mut v_a_8605_: *mut leanh::LeanObject,
    mut v_a_8606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8607_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(
        v_es_8598_,
        v_givenNames_8599_,
        v_k_8600_,
        v_config_8601_,
        v_a_8602_,
        v_a_8603_,
        v_a_8604_,
        v_a_8605_,
    );
    leanh::lean_dec(v_a_8605_);
    leanh::lean_dec_ref(v_a_8604_);
    leanh::lean_dec(v_a_8603_);
    leanh::lean_dec_ref(v_a_8602_);
    leanh::lean_dec_ref(v_config_8601_);
    return v_res_8607_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(
    mut v_00_u03b1_8608_: *mut leanh::LeanObject,
    mut v_es_8609_: *mut leanh::LeanObject,
    mut v_givenNames_8610_: *mut leanh::LeanObject,
    mut v_k_8611_: *mut leanh::LeanObject,
    mut v_config_8612_: *mut leanh::LeanObject,
    mut v_a_8613_: *mut leanh::LeanObject,
    mut v_a_8614_: *mut leanh::LeanObject,
    mut v_a_8615_: *mut leanh::LeanObject,
    mut v_a_8616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8618_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(
        v_es_8609_,
        v_givenNames_8610_,
        v_k_8611_,
        v_config_8612_,
        v_a_8613_,
        v_a_8614_,
        v_a_8615_,
        v_a_8616_,
    );
    return v___x_8618_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___boxed(
    mut v_00_u03b1_8619_: *mut leanh::LeanObject,
    mut v_es_8620_: *mut leanh::LeanObject,
    mut v_givenNames_8621_: *mut leanh::LeanObject,
    mut v_k_8622_: *mut leanh::LeanObject,
    mut v_config_8623_: *mut leanh::LeanObject,
    mut v_a_8624_: *mut leanh::LeanObject,
    mut v_a_8625_: *mut leanh::LeanObject,
    mut v_a_8626_: *mut leanh::LeanObject,
    mut v_a_8627_: *mut leanh::LeanObject,
    mut v_a_8628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8629_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(
        v_00_u03b1_8619_,
        v_es_8620_,
        v_givenNames_8621_,
        v_k_8622_,
        v_config_8623_,
        v_a_8624_,
        v_a_8625_,
        v_a_8626_,
        v_a_8627_,
    );
    leanh::lean_dec(v_a_8627_);
    leanh::lean_dec_ref(v_a_8626_);
    leanh::lean_dec(v_a_8625_);
    leanh::lean_dec_ref(v_a_8624_);
    leanh::lean_dec_ref(v_config_8623_);
    return v_res_8629_;
}
pub unsafe fn l_Lean_Meta_extractLets___redArg___lam__0(
    mut v_k_8630_: *mut leanh::LeanObject,
    mut v_runInBase_8631_: *mut leanh::LeanObject,
    mut v_b_8632_: *mut leanh::LeanObject,
    mut v_c_8633_: *mut leanh::LeanObject,
    mut v_d_8634_: *mut leanh::LeanObject,
    mut v___y_8635_: *mut leanh::LeanObject,
    mut v___y_8636_: *mut leanh::LeanObject,
    mut v___y_8637_: *mut leanh::LeanObject,
    mut v___y_8638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8640_ = leanh::lean_apply_3(v_k_8630_, v_b_8632_, v_c_8633_, v_d_8634_);
    leanh::lean_inc(v___y_8638_);
    leanh::lean_inc_ref(v___y_8637_);
    leanh::lean_inc(v___y_8636_);
    leanh::lean_inc_ref(v___y_8635_);
    v___x_8641_ = leanh::lean_apply_7(
        v_runInBase_8631_,
        leanh::lean_box(0),
        v___x_8640_,
        v___y_8635_,
        v___y_8636_,
        v___y_8637_,
        v___y_8638_,
        leanh::lean_box(0),
    );
    return v___x_8641_;
}
pub unsafe fn l_Lean_Meta_extractLets___redArg___lam__0___boxed(
    mut v_k_8642_: *mut leanh::LeanObject,
    mut v_runInBase_8643_: *mut leanh::LeanObject,
    mut v_b_8644_: *mut leanh::LeanObject,
    mut v_c_8645_: *mut leanh::LeanObject,
    mut v_d_8646_: *mut leanh::LeanObject,
    mut v___y_8647_: *mut leanh::LeanObject,
    mut v___y_8648_: *mut leanh::LeanObject,
    mut v___y_8649_: *mut leanh::LeanObject,
    mut v___y_8650_: *mut leanh::LeanObject,
    mut v___y_8651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8652_ = l_Lean_Meta_extractLets___redArg___lam__0(
        v_k_8642_,
        v_runInBase_8643_,
        v_b_8644_,
        v_c_8645_,
        v_d_8646_,
        v___y_8647_,
        v___y_8648_,
        v___y_8649_,
        v___y_8650_,
    );
    leanh::lean_dec(v___y_8650_);
    leanh::lean_dec_ref(v___y_8649_);
    leanh::lean_dec(v___y_8648_);
    leanh::lean_dec_ref(v___y_8647_);
    return v_res_8652_;
}
pub unsafe fn l_Lean_Meta_extractLets___redArg___lam__1(
    mut v_k_8653_: *mut leanh::LeanObject,
    mut v_es_8654_: *mut leanh::LeanObject,
    mut v_givenNames_8655_: *mut leanh::LeanObject,
    mut v_config_8656_: *mut leanh::LeanObject,
    mut v_runInBase_8657_: *mut leanh::LeanObject,
    mut v___y_8658_: *mut leanh::LeanObject,
    mut v___y_8659_: *mut leanh::LeanObject,
    mut v___y_8660_: *mut leanh::LeanObject,
    mut v___y_8661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_8663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_8663_ = leanh::lean_alloc_closure(
        l_Lean_Meta_extractLets___redArg___lam__0___boxed as *mut core::ffi::c_void,
        10,
        2,
    );
    leanh::lean_closure_set(v___f_8663_, 0, v_k_8653_);
    leanh::lean_closure_set(v___f_8663_, 1, v_runInBase_8657_);
    v___x_8664_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(
        v_es_8654_,
        v_givenNames_8655_,
        v___f_8663_,
        v_config_8656_,
        v___y_8658_,
        v___y_8659_,
        v___y_8660_,
        v___y_8661_,
    );
    return v___x_8664_;
}
pub unsafe fn l_Lean_Meta_extractLets___redArg___lam__1___boxed(
    mut v_k_8665_: *mut leanh::LeanObject,
    mut v_es_8666_: *mut leanh::LeanObject,
    mut v_givenNames_8667_: *mut leanh::LeanObject,
    mut v_config_8668_: *mut leanh::LeanObject,
    mut v_runInBase_8669_: *mut leanh::LeanObject,
    mut v___y_8670_: *mut leanh::LeanObject,
    mut v___y_8671_: *mut leanh::LeanObject,
    mut v___y_8672_: *mut leanh::LeanObject,
    mut v___y_8673_: *mut leanh::LeanObject,
    mut v___y_8674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8675_ = l_Lean_Meta_extractLets___redArg___lam__1(
        v_k_8665_,
        v_es_8666_,
        v_givenNames_8667_,
        v_config_8668_,
        v_runInBase_8669_,
        v___y_8670_,
        v___y_8671_,
        v___y_8672_,
        v___y_8673_,
    );
    leanh::lean_dec(v___y_8673_);
    leanh::lean_dec_ref(v___y_8672_);
    leanh::lean_dec(v___y_8671_);
    leanh::lean_dec_ref(v___y_8670_);
    leanh::lean_dec_ref(v_config_8668_);
    return v_res_8675_;
}
pub unsafe fn l_Lean_Meta_extractLets___redArg(
    mut v_inst_8676_: *mut leanh::LeanObject,
    mut v_inst_8677_: *mut leanh::LeanObject,
    mut v_es_8678_: *mut leanh::LeanObject,
    mut v_givenNames_8679_: *mut leanh::LeanObject,
    mut v_k_8680_: *mut leanh::LeanObject,
    mut v_config_8681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_8682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_liftWith_8683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreM_8684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_8682_ = leanh::lean_ctor_get(v_inst_8676_, 1);
    leanh::lean_inc(v_toBind_8682_);
    leanh::lean_dec_ref(v_inst_8676_);
    v_liftWith_8683_ = leanh::lean_ctor_get(v_inst_8677_, 0);
    leanh::lean_inc(v_liftWith_8683_);
    v_restoreM_8684_ = leanh::lean_ctor_get(v_inst_8677_, 1);
    leanh::lean_inc(v_restoreM_8684_);
    leanh::lean_dec_ref(v_inst_8677_);
    v___f_8685_ = leanh::lean_alloc_closure(
        l_Lean_Meta_extractLets___redArg___lam__1___boxed as *mut core::ffi::c_void,
        10,
        4,
    );
    leanh::lean_closure_set(v___f_8685_, 0, v_k_8680_);
    leanh::lean_closure_set(v___f_8685_, 1, v_es_8678_);
    leanh::lean_closure_set(v___f_8685_, 2, v_givenNames_8679_);
    leanh::lean_closure_set(v___f_8685_, 3, v_config_8681_);
    v___x_8686_ =
        leanh::lean_apply_2(v_liftWith_8683_, leanh::lean_box(0), v___f_8685_);
    v___x_8687_ = leanh::lean_apply_1(v_restoreM_8684_, leanh::lean_box(0));
    v___x_8688_ = leanh::lean_apply_4(
        v_toBind_8682_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_8686_,
        v___x_8687_,
    );
    return v___x_8688_;
}
pub unsafe fn l_Lean_Meta_extractLets(
    mut v_m_8689_: *mut leanh::LeanObject,
    mut v_00_u03b1_8690_: *mut leanh::LeanObject,
    mut v_inst_8691_: *mut leanh::LeanObject,
    mut v_inst_8692_: *mut leanh::LeanObject,
    mut v_es_8693_: *mut leanh::LeanObject,
    mut v_givenNames_8694_: *mut leanh::LeanObject,
    mut v_k_8695_: *mut leanh::LeanObject,
    mut v_config_8696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8697_ = l_Lean_Meta_extractLets___redArg(
        v_inst_8691_,
        v_inst_8692_,
        v_es_8693_,
        v_givenNames_8694_,
        v_k_8695_,
        v_config_8696_,
    );
    return v___x_8697_;
}
pub unsafe fn _init_l_Lean_Meta_liftLets___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_8698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8698_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once
        ),
        _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1,
    );
    v___x_8699_ = l_Lean_Meta_ExtractLets_instInhabitedState_default___closed__0;
    v___x_8700_ = leanh::lean_box(0);
    v___x_8701_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_8701_, 0, v___x_8700_);
    leanh::lean_ctor_set(v___x_8701_, 1, v___x_8699_);
    leanh::lean_ctor_set(v___x_8701_, 2, v___x_8698_);
    return v___x_8701_;
}
pub unsafe fn l_Lean_Meta_liftLets(
    mut v_e_8702_: *mut leanh::LeanObject,
    mut v_config_8703_: *mut leanh::LeanObject,
    mut v_a_8704_: *mut leanh::LeanObject,
    mut v_a_8705_: *mut leanh::LeanObject,
    mut v_a_8706_: *mut leanh::LeanObject,
    mut v_a_8707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofs_8714_: u8 = 0;
    let mut v_types_8715_: u8 = 0;
    let mut v_implicits_8716_: u8 = 0;
    let mut v_descend_8717_: u8 = 0;
    let mut v_underBinder_8718_: u8 = 0;
    let mut v_usedOnly_8719_: u8 = 0;
    let mut v_merge_8720_: u8 = 0;
    let mut v_useContext_8721_: u8 = 0;
    let mut v_preserveBinderNames_8722_: u8 = 0;
    let mut v_lift_8723_: u8 = 0;
    let mut v___x_8725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8726_: u8 = 0;
    let mut v___x_8727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8730_: u8 = 0;
    let mut v___x_8732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8737_: u8 = 0;
    let mut v___x_8738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_8740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8747_: u8 = 0;
    let mut v_a_8748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8751_: u8 = 0;
    let mut v___x_8753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8755_: u8 = 0;
    let mut v_reuseFailAlloc_8756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8757_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8709_ = leanh::lean_unsigned_to_nat(0);
                v___x_8710_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg___closed__1);
                v___x_8711_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_liftLets___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_liftLets___closed__0_once),
                    _init_l_Lean_Meta_liftLets___closed__0,
                );
                v___x_8712_ = lean_st_mk_ref(v___x_8711_);
                v___x_8713_ = lean_st_mk_ref(v___x_8710_);
                v_proofs_8714_ = leanh::lean_ctor_get_uint8(v_config_8703_, 0 as u32);
                v_types_8715_ = leanh::lean_ctor_get_uint8(v_config_8703_, 1 as u32);
                v_implicits_8716_ = leanh::lean_ctor_get_uint8(v_config_8703_, 2 as u32);
                v_descend_8717_ = leanh::lean_ctor_get_uint8(v_config_8703_, 3 as u32);
                v_underBinder_8718_ = leanh::lean_ctor_get_uint8(v_config_8703_, 4 as u32);
                v_usedOnly_8719_ = leanh::lean_ctor_get_uint8(v_config_8703_, 5 as u32);
                v_merge_8720_ = leanh::lean_ctor_get_uint8(v_config_8703_, 6 as u32);
                v_useContext_8721_ = leanh::lean_ctor_get_uint8(v_config_8703_, 7 as u32);
                v_preserveBinderNames_8722_ =
                    leanh::lean_ctor_get_uint8(v_config_8703_, 9 as u32);
                v_lift_8723_ = leanh::lean_ctor_get_uint8(v_config_8703_, 10 as u32);
                v_isSharedCheck_8757_ = (!leanh::lean_is_exclusive(v_config_8703_)) as u8;
                if v_isSharedCheck_8757_ == 0 {
                    v___x_8725_ = v_config_8703_;
                    v_isShared_8726_ = v_isSharedCheck_8757_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_config_8703_);
                    v___x_8725_ = leanh::lean_box(0);
                    v_isShared_8726_ = v_isSharedCheck_8757_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8727_ = leanh::lean_unsigned_to_nat(1);
                v___x_8728_ = lean_mk_empty_array_with_capacity(v___x_8727_);
                v___x_8729_ = lean_array_push(v___x_8728_, v_e_8702_);
                v___x_8730_ = 1;
                if v_isShared_8726_ == 0 {
                    v___x_8732_ = v___x_8725_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8756_ = leanh::lean_alloc_ctor(0, 0, (11) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8756_,
                        0 as u32,
                        v_proofs_8714_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8756_,
                        1 as u32,
                        v_types_8715_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8756_,
                        2 as u32,
                        v_implicits_8716_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8756_,
                        3 as u32,
                        v_descend_8717_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8756_,
                        4 as u32,
                        v_underBinder_8718_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8756_,
                        5 as u32,
                        v_usedOnly_8719_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8756_,
                        6 as u32,
                        v_merge_8720_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8756_,
                        7 as u32,
                        v_useContext_8721_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8756_,
                        9 as u32,
                        v_preserveBinderNames_8722_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8756_,
                        10 as u32,
                        v_lift_8723_,
                    );
                    v___x_8732_ = v_reuseFailAlloc_8756_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(v___x_8732_, 8 as u32, v___x_8730_);
                v___x_8733_ = l_Lean_Meta_ExtractLets_extract(
                    v___x_8729_,
                    v___x_8732_,
                    v___x_8713_,
                    v___x_8712_,
                    v_a_8704_,
                    v_a_8705_,
                    v_a_8706_,
                    v_a_8707_,
                );
                leanh::lean_dec_ref(v___x_8732_);
                if leanh::lean_obj_tag(v___x_8733_) == 0 {
                    v_a_8734_ = leanh::lean_ctor_get(v___x_8733_, 0);
                    v_isSharedCheck_8747_ = (!leanh::lean_is_exclusive(v___x_8733_)) as u8;
                    if v_isSharedCheck_8747_ == 0 {
                        v___x_8736_ = v___x_8733_;
                        v_isShared_8737_ = v_isSharedCheck_8747_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8734_);
                        leanh::lean_dec(v___x_8733_);
                        v___x_8736_ = leanh::lean_box(0);
                        v_isShared_8737_ = v_isSharedCheck_8747_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_8713_);
                    leanh::lean_dec(v___x_8712_);
                    v_a_8748_ = leanh::lean_ctor_get(v___x_8733_, 0);
                    v_isSharedCheck_8755_ = (!leanh::lean_is_exclusive(v___x_8733_)) as u8;
                    if v_isSharedCheck_8755_ == 0 {
                        v___x_8750_ = v___x_8733_;
                        v_isShared_8751_ = v_isSharedCheck_8755_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8748_);
                        leanh::lean_dec(v___x_8733_);
                        v___x_8750_ = leanh::lean_box(0);
                        v_isShared_8751_ = v_isSharedCheck_8755_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_8738_ = lean_st_ref_get(v___x_8713_);
                leanh::lean_dec(v___x_8713_);
                leanh::lean_dec(v___x_8738_);
                v___x_8739_ = lean_st_ref_get(v___x_8712_);
                leanh::lean_dec(v___x_8712_);
                v_decls_8740_ = leanh::lean_ctor_get(v___x_8739_, 1);
                leanh::lean_inc_ref(v_decls_8740_);
                leanh::lean_dec(v___x_8739_);
                v___x_8741_ = l_Lean_instInhabitedExpr;
                v___x_8742_ = lean_array_get(v___x_8741_, v_a_8734_, v___x_8709_);
                leanh::lean_dec(v_a_8734_);
                v___x_8743_ = l_Lean_Meta_ExtractLets_mkLetDecls(v_decls_8740_, v___x_8742_);
                leanh::lean_dec_ref(v_decls_8740_);
                if v_isShared_8737_ == 0 {
                    leanh::lean_ctor_set(v___x_8736_, 0, v___x_8743_);
                    v___x_8745_ = v___x_8736_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8746_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8746_, 0, v___x_8743_);
                    v___x_8745_ = v_reuseFailAlloc_8746_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8745_;
            }
            5 => {
                if v_isShared_8751_ == 0 {
                    v___x_8753_ = v___x_8750_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8754_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8754_, 0, v_a_8748_);
                    v___x_8753_ = v_reuseFailAlloc_8754_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8753_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_liftLets___boxed(
    mut v_e_8758_: *mut leanh::LeanObject,
    mut v_config_8759_: *mut leanh::LeanObject,
    mut v_a_8760_: *mut leanh::LeanObject,
    mut v_a_8761_: *mut leanh::LeanObject,
    mut v_a_8762_: *mut leanh::LeanObject,
    mut v_a_8763_: *mut leanh::LeanObject,
    mut v_a_8764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8765_ = l_Lean_Meta_liftLets(
        v_e_8758_,
        v_config_8759_,
        v_a_8760_,
        v_a_8761_,
        v_a_8762_,
        v_a_8763_,
    );
    leanh::lean_dec(v_a_8763_);
    leanh::lean_dec_ref(v_a_8762_);
    leanh::lean_dec(v_a_8761_);
    leanh::lean_dec_ref(v_a_8760_);
    return v_res_8765_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_8767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8767_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__0;
    v___x_8768_ = l_Lean_stringToMessageData(v___x_8767_);
    return v___x_8768_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_8769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8770_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8769_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1_once
        ),
        _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__1,
    );
    v___x_8770_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_8770_, 0, v___x_8769_);
    return v___x_8770_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(
    mut v_tactic_8771_: *mut leanh::LeanObject,
    mut v_mvarId_8772_: *mut leanh::LeanObject,
    mut v_a_8773_: *mut leanh::LeanObject,
    mut v_a_8774_: *mut leanh::LeanObject,
    mut v_a_8775_: *mut leanh::LeanObject,
    mut v_a_8776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8778_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2_once
        ),
        _init_l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___closed__2,
    );
    v___x_8779_ = l_Lean_Meta_throwTacticEx___redArg(
        v_tactic_8771_,
        v_mvarId_8772_,
        v___x_8778_,
        v_a_8773_,
        v_a_8774_,
        v_a_8775_,
        v_a_8776_,
    );
    return v___x_8779_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg___boxed(
    mut v_tactic_8780_: *mut leanh::LeanObject,
    mut v_mvarId_8781_: *mut leanh::LeanObject,
    mut v_a_8782_: *mut leanh::LeanObject,
    mut v_a_8783_: *mut leanh::LeanObject,
    mut v_a_8784_: *mut leanh::LeanObject,
    mut v_a_8785_: *mut leanh::LeanObject,
    mut v_a_8786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8787_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(
        v_tactic_8780_,
        v_mvarId_8781_,
        v_a_8782_,
        v_a_8783_,
        v_a_8784_,
        v_a_8785_,
    );
    leanh::lean_dec(v_a_8785_);
    leanh::lean_dec_ref(v_a_8784_);
    leanh::lean_dec(v_a_8783_);
    leanh::lean_dec_ref(v_a_8782_);
    return v_res_8787_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(
    mut v_00_u03b1_8788_: *mut leanh::LeanObject,
    mut v_tactic_8789_: *mut leanh::LeanObject,
    mut v_mvarId_8790_: *mut leanh::LeanObject,
    mut v_a_8791_: *mut leanh::LeanObject,
    mut v_a_8792_: *mut leanh::LeanObject,
    mut v_a_8793_: *mut leanh::LeanObject,
    mut v_a_8794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8796_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(
        v_tactic_8789_,
        v_mvarId_8790_,
        v_a_8791_,
        v_a_8792_,
        v_a_8793_,
        v_a_8794_,
    );
    return v___x_8796_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___boxed(
    mut v_00_u03b1_8797_: *mut leanh::LeanObject,
    mut v_tactic_8798_: *mut leanh::LeanObject,
    mut v_mvarId_8799_: *mut leanh::LeanObject,
    mut v_a_8800_: *mut leanh::LeanObject,
    mut v_a_8801_: *mut leanh::LeanObject,
    mut v_a_8802_: *mut leanh::LeanObject,
    mut v_a_8803_: *mut leanh::LeanObject,
    mut v_a_8804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8805_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress(
        v_00_u03b1_8797_,
        v_tactic_8798_,
        v_mvarId_8799_,
        v_a_8800_,
        v_a_8801_,
        v_a_8802_,
        v_a_8803_,
    );
    leanh::lean_dec(v_a_8803_);
    leanh::lean_dec_ref(v_a_8802_);
    leanh::lean_dec(v_a_8801_);
    leanh::lean_dec_ref(v_a_8800_);
    return v_res_8805_;
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(
    mut v_k_8806_: *mut leanh::LeanObject,
    mut v_b_8807_: *mut leanh::LeanObject,
    mut v_c_8808_: *mut leanh::LeanObject,
    mut v_d_8809_: *mut leanh::LeanObject,
    mut v___y_8810_: *mut leanh::LeanObject,
    mut v___y_8811_: *mut leanh::LeanObject,
    mut v___y_8812_: *mut leanh::LeanObject,
    mut v___y_8813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8815_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_8813_);
    leanh::lean_inc_ref(v___y_8812_);
    leanh::lean_inc(v___y_8811_);
    leanh::lean_inc_ref(v___y_8810_);
    v___x_8815_ = leanh::lean_apply_8(
        v_k_8806_,
        v_b_8807_,
        v_c_8808_,
        v_d_8809_,
        v___y_8810_,
        v___y_8811_,
        v___y_8812_,
        v___y_8813_,
        leanh::lean_box(0),
    );
    return v___x_8815_;
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed(
    mut v_k_8816_: *mut leanh::LeanObject,
    mut v_b_8817_: *mut leanh::LeanObject,
    mut v_c_8818_: *mut leanh::LeanObject,
    mut v_d_8819_: *mut leanh::LeanObject,
    mut v___y_8820_: *mut leanh::LeanObject,
    mut v___y_8821_: *mut leanh::LeanObject,
    mut v___y_8822_: *mut leanh::LeanObject,
    mut v___y_8823_: *mut leanh::LeanObject,
    mut v___y_8824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8825_ =
        l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0(
            v_k_8816_,
            v_b_8817_,
            v_c_8818_,
            v_d_8819_,
            v___y_8820_,
            v___y_8821_,
            v___y_8822_,
            v___y_8823_,
        );
    leanh::lean_dec(v___y_8823_);
    leanh::lean_dec_ref(v___y_8822_);
    leanh::lean_dec(v___y_8821_);
    leanh::lean_dec_ref(v___y_8820_);
    return v_res_8825_;
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(
    mut v_es_8826_: *mut leanh::LeanObject,
    mut v_givenNames_8827_: *mut leanh::LeanObject,
    mut v_k_8828_: *mut leanh::LeanObject,
    mut v_config_8829_: *mut leanh::LeanObject,
    mut v___y_8830_: *mut leanh::LeanObject,
    mut v___y_8831_: *mut leanh::LeanObject,
    mut v___y_8832_: *mut leanh::LeanObject,
    mut v___y_8833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_8835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8840_: u8 = 0;
    let mut v___x_8842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8844_: u8 = 0;
    let mut v_a_8845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8848_: u8 = 0;
    let mut v___x_8850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8852_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_8835_ = leanh::lean_alloc_closure(l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 1);
                leanh::lean_closure_set(v___f_8835_, 0, v_k_8828_);
                v___x_8836_ =
                    l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp___redArg(
                        v_es_8826_,
                        v_givenNames_8827_,
                        v___f_8835_,
                        v_config_8829_,
                        v___y_8830_,
                        v___y_8831_,
                        v___y_8832_,
                        v___y_8833_,
                    );
                if leanh::lean_obj_tag(v___x_8836_) == 0 {
                    v_a_8837_ = leanh::lean_ctor_get(v___x_8836_, 0);
                    v_isSharedCheck_8844_ = (!leanh::lean_is_exclusive(v___x_8836_)) as u8;
                    if v_isSharedCheck_8844_ == 0 {
                        v___x_8839_ = v___x_8836_;
                        v_isShared_8840_ = v_isSharedCheck_8844_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8837_);
                        leanh::lean_dec(v___x_8836_);
                        v___x_8839_ = leanh::lean_box(0);
                        v_isShared_8840_ = v_isSharedCheck_8844_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8845_ = leanh::lean_ctor_get(v___x_8836_, 0);
                    v_isSharedCheck_8852_ = (!leanh::lean_is_exclusive(v___x_8836_)) as u8;
                    if v_isSharedCheck_8852_ == 0 {
                        v___x_8847_ = v___x_8836_;
                        v_isShared_8848_ = v_isSharedCheck_8852_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8845_);
                        leanh::lean_dec(v___x_8836_);
                        v___x_8847_ = leanh::lean_box(0);
                        v_isShared_8848_ = v_isSharedCheck_8852_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8840_ == 0 {
                    v___x_8842_ = v___x_8839_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8843_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8843_, 0, v_a_8837_);
                    v___x_8842_ = v_reuseFailAlloc_8843_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8842_;
            }
            3 => {
                if v_isShared_8848_ == 0 {
                    v___x_8850_ = v___x_8847_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8851_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8851_, 0, v_a_8845_);
                    v___x_8850_ = v_reuseFailAlloc_8851_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8850_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg___boxed(
    mut v_es_8853_: *mut leanh::LeanObject,
    mut v_givenNames_8854_: *mut leanh::LeanObject,
    mut v_k_8855_: *mut leanh::LeanObject,
    mut v_config_8856_: *mut leanh::LeanObject,
    mut v___y_8857_: *mut leanh::LeanObject,
    mut v___y_8858_: *mut leanh::LeanObject,
    mut v___y_8859_: *mut leanh::LeanObject,
    mut v___y_8860_: *mut leanh::LeanObject,
    mut v___y_8861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8862_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(
        v_es_8853_,
        v_givenNames_8854_,
        v_k_8855_,
        v_config_8856_,
        v___y_8857_,
        v___y_8858_,
        v___y_8859_,
        v___y_8860_,
    );
    leanh::lean_dec(v___y_8860_);
    leanh::lean_dec_ref(v___y_8859_);
    leanh::lean_dec(v___y_8858_);
    leanh::lean_dec_ref(v___y_8857_);
    leanh::lean_dec_ref(v_config_8856_);
    return v_res_8862_;
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(
    mut v_00_u03b1_8863_: *mut leanh::LeanObject,
    mut v_es_8864_: *mut leanh::LeanObject,
    mut v_givenNames_8865_: *mut leanh::LeanObject,
    mut v_k_8866_: *mut leanh::LeanObject,
    mut v_config_8867_: *mut leanh::LeanObject,
    mut v___y_8868_: *mut leanh::LeanObject,
    mut v___y_8869_: *mut leanh::LeanObject,
    mut v___y_8870_: *mut leanh::LeanObject,
    mut v___y_8871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8873_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(
        v_es_8864_,
        v_givenNames_8865_,
        v_k_8866_,
        v_config_8867_,
        v___y_8868_,
        v___y_8869_,
        v___y_8870_,
        v___y_8871_,
    );
    return v___x_8873_;
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___boxed(
    mut v_00_u03b1_8874_: *mut leanh::LeanObject,
    mut v_es_8875_: *mut leanh::LeanObject,
    mut v_givenNames_8876_: *mut leanh::LeanObject,
    mut v_k_8877_: *mut leanh::LeanObject,
    mut v_config_8878_: *mut leanh::LeanObject,
    mut v___y_8879_: *mut leanh::LeanObject,
    mut v___y_8880_: *mut leanh::LeanObject,
    mut v___y_8881_: *mut leanh::LeanObject,
    mut v___y_8882_: *mut leanh::LeanObject,
    mut v___y_8883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8884_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2(
        v_00_u03b1_8874_,
        v_es_8875_,
        v_givenNames_8876_,
        v_k_8877_,
        v_config_8878_,
        v___y_8879_,
        v___y_8880_,
        v___y_8881_,
        v___y_8882_,
    );
    leanh::lean_dec(v___y_8882_);
    leanh::lean_dec_ref(v___y_8881_);
    leanh::lean_dec(v___y_8880_);
    leanh::lean_dec_ref(v___y_8879_);
    leanh::lean_dec_ref(v_config_8878_);
    return v_res_8884_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(
    mut v_mvarId_8885_: *mut leanh::LeanObject,
    mut v_x_8886_: *mut leanh::LeanObject,
    mut v___y_8887_: *mut leanh::LeanObject,
    mut v___y_8888_: *mut leanh::LeanObject,
    mut v___y_8889_: *mut leanh::LeanObject,
    mut v___y_8890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8896_: u8 = 0;
    let mut v___x_8898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8900_: u8 = 0;
    let mut v_a_8901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8904_: u8 = 0;
    let mut v___x_8906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8892_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_8885_,
                    v_x_8886_,
                    v___y_8887_,
                    v___y_8888_,
                    v___y_8889_,
                    v___y_8890_,
                );
                if leanh::lean_obj_tag(v___x_8892_) == 0 {
                    v_a_8893_ = leanh::lean_ctor_get(v___x_8892_, 0);
                    v_isSharedCheck_8900_ = (!leanh::lean_is_exclusive(v___x_8892_)) as u8;
                    if v_isSharedCheck_8900_ == 0 {
                        v___x_8895_ = v___x_8892_;
                        v_isShared_8896_ = v_isSharedCheck_8900_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8893_);
                        leanh::lean_dec(v___x_8892_);
                        v___x_8895_ = leanh::lean_box(0);
                        v_isShared_8896_ = v_isSharedCheck_8900_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8901_ = leanh::lean_ctor_get(v___x_8892_, 0);
                    v_isSharedCheck_8908_ = (!leanh::lean_is_exclusive(v___x_8892_)) as u8;
                    if v_isSharedCheck_8908_ == 0 {
                        v___x_8903_ = v___x_8892_;
                        v_isShared_8904_ = v_isSharedCheck_8908_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8901_);
                        leanh::lean_dec(v___x_8892_);
                        v___x_8903_ = leanh::lean_box(0);
                        v_isShared_8904_ = v_isSharedCheck_8908_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8896_ == 0 {
                    v___x_8898_ = v___x_8895_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8899_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8899_, 0, v_a_8893_);
                    v___x_8898_ = v_reuseFailAlloc_8899_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8898_;
            }
            3 => {
                if v_isShared_8904_ == 0 {
                    v___x_8906_ = v___x_8903_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8907_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8907_, 0, v_a_8901_);
                    v___x_8906_ = v_reuseFailAlloc_8907_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8906_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg___boxed(
    mut v_mvarId_8909_: *mut leanh::LeanObject,
    mut v_x_8910_: *mut leanh::LeanObject,
    mut v___y_8911_: *mut leanh::LeanObject,
    mut v___y_8912_: *mut leanh::LeanObject,
    mut v___y_8913_: *mut leanh::LeanObject,
    mut v___y_8914_: *mut leanh::LeanObject,
    mut v___y_8915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8916_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(
        v_mvarId_8909_,
        v_x_8910_,
        v___y_8911_,
        v___y_8912_,
        v___y_8913_,
        v___y_8914_,
    );
    leanh::lean_dec(v___y_8914_);
    leanh::lean_dec_ref(v___y_8913_);
    leanh::lean_dec(v___y_8912_);
    leanh::lean_dec_ref(v___y_8911_);
    return v_res_8916_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(
    mut v_00_u03b1_8917_: *mut leanh::LeanObject,
    mut v_mvarId_8918_: *mut leanh::LeanObject,
    mut v_x_8919_: *mut leanh::LeanObject,
    mut v___y_8920_: *mut leanh::LeanObject,
    mut v___y_8921_: *mut leanh::LeanObject,
    mut v___y_8922_: *mut leanh::LeanObject,
    mut v___y_8923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8925_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(
        v_mvarId_8918_,
        v_x_8919_,
        v___y_8920_,
        v___y_8921_,
        v___y_8922_,
        v___y_8923_,
    );
    return v___x_8925_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___boxed(
    mut v_00_u03b1_8926_: *mut leanh::LeanObject,
    mut v_mvarId_8927_: *mut leanh::LeanObject,
    mut v_x_8928_: *mut leanh::LeanObject,
    mut v___y_8929_: *mut leanh::LeanObject,
    mut v___y_8930_: *mut leanh::LeanObject,
    mut v___y_8931_: *mut leanh::LeanObject,
    mut v___y_8932_: *mut leanh::LeanObject,
    mut v___y_8933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8934_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3(
        v_00_u03b1_8926_,
        v_mvarId_8927_,
        v_x_8928_,
        v___y_8929_,
        v___y_8930_,
        v___y_8931_,
        v___y_8932_,
    );
    leanh::lean_dec(v___y_8932_);
    leanh::lean_dec_ref(v___y_8931_);
    leanh::lean_dec(v___y_8930_);
    leanh::lean_dec_ref(v___y_8929_);
    return v_res_8934_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(
    mut v_x_8935_: *mut leanh::LeanObject,
    mut v_x_8936_: *mut leanh::LeanObject,
    mut v_x_8937_: *mut leanh::LeanObject,
    mut v_x_8938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_8939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_8940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8943_: u8 = 0;
    let mut v___x_8944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8945_: u8 = 0;
    let mut v___x_8946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_8951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8952_: u8 = 0;
    let mut v___x_8954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8964_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_8939_ = leanh::lean_ctor_get(v_x_8935_, 0);
                v_vs_8940_ = leanh::lean_ctor_get(v_x_8935_, 1);
                v_isSharedCheck_8964_ = (!leanh::lean_is_exclusive(v_x_8935_)) as u8;
                if v_isSharedCheck_8964_ == 0 {
                    v___x_8942_ = v_x_8935_;
                    v_isShared_8943_ = v_isSharedCheck_8964_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_8940_);
                    leanh::lean_inc(v_ks_8939_);
                    leanh::lean_dec(v_x_8935_);
                    v___x_8942_ = leanh::lean_box(0);
                    v_isShared_8943_ = v_isSharedCheck_8964_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8944_ = lean_array_get_size(v_ks_8939_);
                v___x_8945_ = lean_nat_dec_lt(v_x_8936_, v___x_8944_);
                if v___x_8945_ == 0 {
                    leanh::lean_dec(v_x_8936_);
                    v___x_8946_ = lean_array_push(v_ks_8939_, v_x_8937_);
                    v___x_8947_ = lean_array_push(v_vs_8940_, v_x_8938_);
                    if v_isShared_8943_ == 0 {
                        leanh::lean_ctor_set(v___x_8942_, 1, v___x_8947_);
                        leanh::lean_ctor_set(v___x_8942_, 0, v___x_8946_);
                        v___x_8949_ = v___x_8942_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8950_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8950_, 0, v___x_8946_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8950_, 1, v___x_8947_);
                        v___x_8949_ = v_reuseFailAlloc_8950_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_8951_ = lean_array_fget_borrowed(v_ks_8939_, v_x_8936_);
                    v___x_8952_ = l_Lean_instBEqMVarId_beq(v_x_8937_, v_k_x27_8951_);
                    if v___x_8952_ == 0 {
                        if v_isShared_8943_ == 0 {
                            v___x_8954_ = v___x_8942_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_8958_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_8958_, 0, v_ks_8939_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_8958_, 1, v_vs_8940_);
                            v___x_8954_ = v_reuseFailAlloc_8958_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_8959_ = lean_array_fset(v_ks_8939_, v_x_8936_, v_x_8937_);
                        v___x_8960_ = lean_array_fset(v_vs_8940_, v_x_8936_, v_x_8938_);
                        leanh::lean_dec(v_x_8936_);
                        if v_isShared_8943_ == 0 {
                            leanh::lean_ctor_set(v___x_8942_, 1, v___x_8960_);
                            leanh::lean_ctor_set(v___x_8942_, 0, v___x_8959_);
                            v___x_8962_ = v___x_8942_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_8963_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_8963_, 0, v___x_8959_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_8963_, 1, v___x_8960_);
                            v___x_8962_ = v_reuseFailAlloc_8963_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_8949_;
            }
            3 => {
                v___x_8955_ = leanh::lean_unsigned_to_nat(1);
                v___x_8956_ = lean_nat_add(v_x_8936_, v___x_8955_);
                leanh::lean_dec(v_x_8936_);
                v_x_8935_ = v___x_8954_;
                v_x_8936_ = v___x_8956_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_8962_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(
    mut v_n_8965_: *mut leanh::LeanObject,
    mut v_k_8966_: *mut leanh::LeanObject,
    mut v_v_8967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8968_ = leanh::lean_unsigned_to_nat(0);
    v___x_8969_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_n_8965_, v___x_8968_, v_k_8966_, v_v_8967_);
    return v___x_8969_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_8970_: usize = 0;
    let mut v___x_8971_: usize = 0;
    let mut v___x_8972_: usize = 0;
    v___x_8970_ = 5usize;
    v___x_8971_ = 1usize;
    v___x_8972_ = lean_usize_shift_left(v___x_8971_, v___x_8970_);
    return v___x_8972_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_8973_: usize = 0;
    let mut v___x_8974_: usize = 0;
    let mut v___x_8975_: usize = 0;
    v___x_8973_ = 1usize;
    v___x_8974_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__0);
    v___x_8975_ = lean_usize_sub(v___x_8974_, v___x_8973_);
    return v___x_8975_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_8976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8976_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_8976_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(
    mut v_x_8977_: *mut leanh::LeanObject,
    mut v_x_8978_: usize,
    mut v_x_8979_: usize,
    mut v_x_8980_: *mut leanh::LeanObject,
    mut v_x_8981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_8982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8983_: usize = 0;
    let mut v___x_8984_: usize = 0;
    let mut v___x_8985_: usize = 0;
    let mut v___x_8986_: usize = 0;
    let mut v_j_8987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8989_: u8 = 0;
    let mut v___x_8991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8992_: u8 = 0;
    let mut v_v_8993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_8995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_9002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_9003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9006_: u8 = 0;
    let mut v___x_9007_: u8 = 0;
    let mut v___x_9008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9013_: u8 = 0;
    let mut v_node_9014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9017_: u8 = 0;
    let mut v___x_9018_: usize = 0;
    let mut v___x_9019_: usize = 0;
    let mut v___x_9020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9024_: u8 = 0;
    let mut v___x_9025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9026_: u8 = 0;
    let mut v_unused_9027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_9028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_9029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9032_: u8 = 0;
    let mut v___x_9034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_9035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9037_: u8 = 0;
    let mut v_ks_9038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_9039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9043_: usize = 0;
    let mut v___x_9044_: u8 = 0;
    let mut v___x_9045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9047_: u8 = 0;
    let mut v_reuseFailAlloc_9048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9049_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_8977_) == 0 {
                    v_es_8982_ = leanh::lean_ctor_get(v_x_8977_, 0);
                    v___x_8983_ = 5usize;
                    v___x_8984_ = 1usize;
                    v___x_8985_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__1);
                    v___x_8986_ = lean_usize_land(v_x_8978_, v___x_8985_);
                    v_j_8987_ = lean_usize_to_nat(v___x_8986_);
                    v___x_8988_ = lean_array_get_size(v_es_8982_);
                    v___x_8989_ = lean_nat_dec_lt(v_j_8987_, v___x_8988_);
                    if v___x_8989_ == 0 {
                        leanh::lean_dec(v_j_8987_);
                        leanh::lean_dec(v_x_8981_);
                        leanh::lean_dec(v_x_8980_);
                        return v_x_8977_;
                    } else {
                        leanh::lean_inc_ref(v_es_8982_);
                        v_isSharedCheck_9026_ = (!leanh::lean_is_exclusive(v_x_8977_)) as u8;
                        if v_isSharedCheck_9026_ == 0 {
                            v_unused_9027_ = leanh::lean_ctor_get(v_x_8977_, 0);
                            leanh::lean_dec(v_unused_9027_);
                            v___x_8991_ = v_x_8977_;
                            v_isShared_8992_ = v_isSharedCheck_9026_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_8977_);
                            v___x_8991_ = leanh::lean_box(0);
                            v_isShared_8992_ = v_isSharedCheck_9026_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_9028_ = leanh::lean_ctor_get(v_x_8977_, 0);
                    v_vs_9029_ = leanh::lean_ctor_get(v_x_8977_, 1);
                    v_isSharedCheck_9049_ = (!leanh::lean_is_exclusive(v_x_8977_)) as u8;
                    if v_isSharedCheck_9049_ == 0 {
                        v___x_9031_ = v_x_8977_;
                        v_isShared_9032_ = v_isSharedCheck_9049_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_9029_);
                        leanh::lean_inc(v_ks_9028_);
                        leanh::lean_dec(v_x_8977_);
                        v___x_9031_ = leanh::lean_box(0);
                        v_isShared_9032_ = v_isSharedCheck_9049_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_8993_ = lean_array_fget(v_es_8982_, v_j_8987_);
                v___x_8994_ = leanh::lean_box(0);
                v_xs_x27_8995_ = lean_array_fset(v_es_8982_, v_j_8987_, v___x_8994_);
                match leanh::lean_obj_tag(v_v_8993_) {
                    0 => {
                        v_key_9002_ = leanh::lean_ctor_get(v_v_8993_, 0);
                        v_val_9003_ = leanh::lean_ctor_get(v_v_8993_, 1);
                        v_isSharedCheck_9013_ = (!leanh::lean_is_exclusive(v_v_8993_)) as u8;
                        if v_isSharedCheck_9013_ == 0 {
                            v___x_9005_ = v_v_8993_;
                            v_isShared_9006_ = v_isSharedCheck_9013_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_9003_);
                            leanh::lean_inc(v_key_9002_);
                            leanh::lean_dec(v_v_8993_);
                            v___x_9005_ = leanh::lean_box(0);
                            v_isShared_9006_ = v_isSharedCheck_9013_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_9014_ = leanh::lean_ctor_get(v_v_8993_, 0);
                        v_isSharedCheck_9024_ = (!leanh::lean_is_exclusive(v_v_8993_)) as u8;
                        if v_isSharedCheck_9024_ == 0 {
                            v___x_9016_ = v_v_8993_;
                            v_isShared_9017_ = v_isSharedCheck_9024_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_9014_);
                            leanh::lean_dec(v_v_8993_);
                            v___x_9016_ = leanh::lean_box(0);
                            v_isShared_9017_ = v_isSharedCheck_9024_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_9025_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_9025_, 0, v_x_8980_);
                        leanh::lean_ctor_set(v___x_9025_, 1, v_x_8981_);
                        v___y_8997_ = v___x_9025_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_8998_ = lean_array_fset(v_xs_x27_8995_, v_j_8987_, v___y_8997_);
                leanh::lean_dec(v_j_8987_);
                if v_isShared_8992_ == 0 {
                    leanh::lean_ctor_set(v___x_8991_, 0, v___x_8998_);
                    v___x_9000_ = v___x_8991_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9001_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9001_, 0, v___x_8998_);
                    v___x_9000_ = v_reuseFailAlloc_9001_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_9000_;
            }
            4 => {
                v___x_9007_ = l_Lean_instBEqMVarId_beq(v_x_8980_, v_key_9002_);
                if v___x_9007_ == 0 {
                    leanh::lean_del_object(v___x_9005_);
                    v___x_9008_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_9002_,
                        v_val_9003_,
                        v_x_8980_,
                        v_x_8981_,
                    );
                    v___x_9009_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_9009_, 0, v___x_9008_);
                    v___y_8997_ = v___x_9009_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_9003_);
                    leanh::lean_dec(v_key_9002_);
                    if v_isShared_9006_ == 0 {
                        leanh::lean_ctor_set(v___x_9005_, 1, v_x_8981_);
                        leanh::lean_ctor_set(v___x_9005_, 0, v_x_8980_);
                        v___x_9011_ = v___x_9005_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_9012_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_9012_, 0, v_x_8980_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_9012_, 1, v_x_8981_);
                        v___x_9011_ = v_reuseFailAlloc_9012_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_8997_ = v___x_9011_;
                state = 2;
                continue;
            }
            6 => {
                v___x_9018_ = lean_usize_shift_right(v_x_8978_, v___x_8983_);
                v___x_9019_ = lean_usize_add(v_x_8979_, v___x_8984_);
                v___x_9020_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_node_9014_, v___x_9018_, v___x_9019_, v_x_8980_, v_x_8981_);
                if v_isShared_9017_ == 0 {
                    leanh::lean_ctor_set(v___x_9016_, 0, v___x_9020_);
                    v___x_9022_ = v___x_9016_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_9023_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9023_, 0, v___x_9020_);
                    v___x_9022_ = v_reuseFailAlloc_9023_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_8997_ = v___x_9022_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_9032_ == 0 {
                    v___x_9034_ = v___x_9031_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_9048_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9048_, 0, v_ks_9028_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9048_, 1, v_vs_9029_);
                    v___x_9034_ = v_reuseFailAlloc_9048_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_9035_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v___x_9034_, v_x_8980_, v_x_8981_);
                v___x_9043_ = 7usize;
                v___x_9044_ = lean_usize_dec_le(v___x_9043_, v_x_8979_);
                if v___x_9044_ == 0 {
                    v___x_9045_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_9035_);
                    v___x_9046_ = leanh::lean_unsigned_to_nat(4);
                    v___x_9047_ = lean_nat_dec_lt(v___x_9045_, v___x_9046_);
                    leanh::lean_dec(v___x_9045_);
                    v___y_9037_ = v___x_9047_;
                    state = 10;
                    continue;
                } else {
                    v___y_9037_ = v___x_9044_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_9037_ == 0 {
                    v_ks_9038_ = leanh::lean_ctor_get(v_newNode_9035_, 0);
                    leanh::lean_inc_ref(v_ks_9038_);
                    v_vs_9039_ = leanh::lean_ctor_get(v_newNode_9035_, 1);
                    leanh::lean_inc_ref(v_vs_9039_);
                    leanh::lean_dec_ref(v_newNode_9035_);
                    v___x_9040_ = leanh::lean_unsigned_to_nat(0);
                    v___x_9041_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___closed__2);
                    v___x_9042_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_x_8979_, v_ks_9038_, v_vs_9039_, v___x_9040_, v___x_9041_);
                    leanh::lean_dec_ref(v_vs_9039_);
                    leanh::lean_dec_ref(v_ks_9038_);
                    return v___x_9042_;
                } else {
                    return v_newNode_9035_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(
    mut v_depth_9050_: usize,
    mut v_keys_9051_: *mut leanh::LeanObject,
    mut v_vals_9052_: *mut leanh::LeanObject,
    mut v_i_9053_: *mut leanh::LeanObject,
    mut v_entries_9054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9056_: u8 = 0;
    let mut v_k_9057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_9058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9059_: u64 = 0;
    let mut v_h_9060_: usize = 0;
    let mut v___x_9061_: usize = 0;
    let mut v___x_9062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9063_: usize = 0;
    let mut v___x_9064_: usize = 0;
    let mut v___x_9065_: usize = 0;
    let mut v_h_9066_: usize = 0;
    let mut v___x_9067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9055_ = lean_array_get_size(v_keys_9051_);
                v___x_9056_ = lean_nat_dec_lt(v_i_9053_, v___x_9055_);
                if v___x_9056_ == 0 {
                    leanh::lean_dec(v_i_9053_);
                    return v_entries_9054_;
                } else {
                    v_k_9057_ = lean_array_fget_borrowed(v_keys_9051_, v_i_9053_);
                    v_v_9058_ = lean_array_fget_borrowed(v_vals_9052_, v_i_9053_);
                    v___x_9059_ = l_Lean_instHashableMVarId_hash(v_k_9057_);
                    v_h_9060_ = lean_uint64_to_usize(v___x_9059_);
                    v___x_9061_ = 5usize;
                    v___x_9062_ = leanh::lean_unsigned_to_nat(1);
                    v___x_9063_ = 1usize;
                    v___x_9064_ = lean_usize_sub(v_depth_9050_, v___x_9063_);
                    v___x_9065_ = lean_usize_mul(v___x_9061_, v___x_9064_);
                    v_h_9066_ = lean_usize_shift_right(v_h_9060_, v___x_9065_);
                    v___x_9067_ = lean_nat_add(v_i_9053_, v___x_9062_);
                    leanh::lean_dec(v_i_9053_);
                    leanh::lean_inc(v_v_9058_);
                    leanh::lean_inc(v_k_9057_);
                    v___x_9068_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_entries_9054_, v_h_9066_, v_depth_9050_, v_k_9057_, v_v_9058_);
                    v_i_9053_ = v___x_9067_;
                    v_entries_9054_ = v___x_9068_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg___boxed(
    mut v_depth_9070_: *mut leanh::LeanObject,
    mut v_keys_9071_: *mut leanh::LeanObject,
    mut v_vals_9072_: *mut leanh::LeanObject,
    mut v_i_9073_: *mut leanh::LeanObject,
    mut v_entries_9074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_9075_: usize = 0;
    let mut v_res_9076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_9075_ = leanh::lean_unbox_usize(v_depth_9070_);
    leanh::lean_dec(v_depth_9070_);
    v_res_9076_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_boxed_9075_, v_keys_9071_, v_vals_9072_, v_i_9073_, v_entries_9074_);
    leanh::lean_dec_ref(v_vals_9072_);
    leanh::lean_dec_ref(v_keys_9071_);
    return v_res_9076_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg___boxed(
    mut v_x_9077_: *mut leanh::LeanObject,
    mut v_x_9078_: *mut leanh::LeanObject,
    mut v_x_9079_: *mut leanh::LeanObject,
    mut v_x_9080_: *mut leanh::LeanObject,
    mut v_x_9081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2324__boxed_9082_: usize = 0;
    let mut v_x_2325__boxed_9083_: usize = 0;
    let mut v_res_9084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2324__boxed_9082_ = leanh::lean_unbox_usize(v_x_9078_);
    leanh::lean_dec(v_x_9078_);
    v_x_2325__boxed_9083_ = leanh::lean_unbox_usize(v_x_9079_);
    leanh::lean_dec(v_x_9079_);
    v_res_9084_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_9077_, v_x_2324__boxed_9082_, v_x_2325__boxed_9083_, v_x_9080_, v_x_9081_);
    return v_res_9084_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(
    mut v_x_9085_: *mut leanh::LeanObject,
    mut v_x_9086_: *mut leanh::LeanObject,
    mut v_x_9087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9088_: u64 = 0;
    let mut v___x_9089_: usize = 0;
    let mut v___x_9090_: usize = 0;
    let mut v___x_9091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9088_ = l_Lean_instHashableMVarId_hash(v_x_9086_);
    v___x_9089_ = lean_uint64_to_usize(v___x_9088_);
    v___x_9090_ = 1usize;
    v___x_9091_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_9085_, v___x_9089_, v___x_9090_, v_x_9086_, v_x_9087_);
    return v___x_9091_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(
    mut v_mvarId_9092_: *mut leanh::LeanObject,
    mut v_val_9093_: *mut leanh::LeanObject,
    mut v___y_9094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_9097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_9098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_9099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_9100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_9101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9104_: u8 = 0;
    let mut v_depth_9105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_9106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_9107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_9108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_9109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_9110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_9111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_9112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_9113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_9114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9117_: u8 = 0;
    let mut v___x_9118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9128_: u8 = 0;
    let mut v_isSharedCheck_9129_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9096_ = lean_st_ref_take(v___y_9094_);
                v_mctx_9097_ = leanh::lean_ctor_get(v___x_9096_, 0);
                v_cache_9098_ = leanh::lean_ctor_get(v___x_9096_, 1);
                v_zetaDeltaFVarIds_9099_ = leanh::lean_ctor_get(v___x_9096_, 2);
                v_postponed_9100_ = leanh::lean_ctor_get(v___x_9096_, 3);
                v_diag_9101_ = leanh::lean_ctor_get(v___x_9096_, 4);
                v_isSharedCheck_9129_ = (!leanh::lean_is_exclusive(v___x_9096_)) as u8;
                if v_isSharedCheck_9129_ == 0 {
                    v___x_9103_ = v___x_9096_;
                    v_isShared_9104_ = v_isSharedCheck_9129_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_9101_);
                    leanh::lean_inc(v_postponed_9100_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_9099_);
                    leanh::lean_inc(v_cache_9098_);
                    leanh::lean_inc(v_mctx_9097_);
                    leanh::lean_dec(v___x_9096_);
                    v___x_9103_ = leanh::lean_box(0);
                    v_isShared_9104_ = v_isSharedCheck_9129_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_9105_ = leanh::lean_ctor_get(v_mctx_9097_, 0);
                v_levelAssignDepth_9106_ = leanh::lean_ctor_get(v_mctx_9097_, 1);
                v_lmvarCounter_9107_ = leanh::lean_ctor_get(v_mctx_9097_, 2);
                v_mvarCounter_9108_ = leanh::lean_ctor_get(v_mctx_9097_, 3);
                v_lDecls_9109_ = leanh::lean_ctor_get(v_mctx_9097_, 4);
                v_decls_9110_ = leanh::lean_ctor_get(v_mctx_9097_, 5);
                v_userNames_9111_ = leanh::lean_ctor_get(v_mctx_9097_, 6);
                v_lAssignment_9112_ = leanh::lean_ctor_get(v_mctx_9097_, 7);
                v_eAssignment_9113_ = leanh::lean_ctor_get(v_mctx_9097_, 8);
                v_dAssignment_9114_ = leanh::lean_ctor_get(v_mctx_9097_, 9);
                v_isSharedCheck_9128_ = (!leanh::lean_is_exclusive(v_mctx_9097_)) as u8;
                if v_isSharedCheck_9128_ == 0 {
                    v___x_9116_ = v_mctx_9097_;
                    v_isShared_9117_ = v_isSharedCheck_9128_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_9114_);
                    leanh::lean_inc(v_eAssignment_9113_);
                    leanh::lean_inc(v_lAssignment_9112_);
                    leanh::lean_inc(v_userNames_9111_);
                    leanh::lean_inc(v_decls_9110_);
                    leanh::lean_inc(v_lDecls_9109_);
                    leanh::lean_inc(v_mvarCounter_9108_);
                    leanh::lean_inc(v_lmvarCounter_9107_);
                    leanh::lean_inc(v_levelAssignDepth_9106_);
                    leanh::lean_inc(v_depth_9105_);
                    leanh::lean_dec(v_mctx_9097_);
                    v___x_9116_ = leanh::lean_box(0);
                    v_isShared_9117_ = v_isSharedCheck_9128_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9118_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_eAssignment_9113_, v_mvarId_9092_, v_val_9093_);
                if v_isShared_9117_ == 0 {
                    leanh::lean_ctor_set(v___x_9116_, 8, v___x_9118_);
                    v___x_9120_ = v___x_9116_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9127_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9127_, 0, v_depth_9105_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_9127_,
                        1,
                        v_levelAssignDepth_9106_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_9127_, 2, v_lmvarCounter_9107_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9127_, 3, v_mvarCounter_9108_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9127_, 4, v_lDecls_9109_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9127_, 5, v_decls_9110_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9127_, 6, v_userNames_9111_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9127_, 7, v_lAssignment_9112_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9127_, 8, v___x_9118_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9127_, 9, v_dAssignment_9114_);
                    v___x_9120_ = v_reuseFailAlloc_9127_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_9104_ == 0 {
                    leanh::lean_ctor_set(v___x_9103_, 0, v___x_9120_);
                    v___x_9122_ = v___x_9103_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9126_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9126_, 0, v___x_9120_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9126_, 1, v_cache_9098_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_9126_,
                        2,
                        v_zetaDeltaFVarIds_9099_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_9126_, 3, v_postponed_9100_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9126_, 4, v_diag_9101_);
                    v___x_9122_ = v_reuseFailAlloc_9126_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_9123_ = lean_st_ref_set(v___y_9094_, v___x_9122_);
                v___x_9124_ = leanh::lean_box(0);
                v___x_9125_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_9125_, 0, v___x_9124_);
                return v___x_9125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg___boxed(
    mut v_mvarId_9130_: *mut leanh::LeanObject,
    mut v_val_9131_: *mut leanh::LeanObject,
    mut v___y_9132_: *mut leanh::LeanObject,
    mut v___y_9133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9134_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(
        v_mvarId_9130_,
        v_val_9131_,
        v___y_9132_,
    );
    leanh::lean_dec(v___y_9132_);
    return v_res_9134_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(
    mut v_sz_9135_: usize,
    mut v_i_9136_: usize,
    mut v_bs_9137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9138_: u8 = 0;
    let mut v_v_9139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_9141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9143_: usize = 0;
    let mut v___x_9144_: usize = 0;
    let mut v___x_9145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9138_ = lean_usize_dec_lt(v_i_9136_, v_sz_9135_);
                if v___x_9138_ == 0 {
                    return v_bs_9137_;
                } else {
                    v_v_9139_ = lean_array_uget(v_bs_9137_, v_i_9136_);
                    v___x_9140_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_9141_ = lean_array_uset(v_bs_9137_, v_i_9136_, v___x_9140_);
                    v___x_9142_ = l_Lean_Expr_fvar___override(v_v_9139_);
                    v___x_9143_ = 1usize;
                    v___x_9144_ = lean_usize_add(v_i_9136_, v___x_9143_);
                    v___x_9145_ = lean_array_uset(v_bs_x27_9141_, v_i_9136_, v___x_9142_);
                    v_i_9136_ = v___x_9144_;
                    v_bs_9137_ = v___x_9145_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0___boxed(
    mut v_sz_9147_: *mut leanh::LeanObject,
    mut v_i_9148_: *mut leanh::LeanObject,
    mut v_bs_9149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_9150_: usize = 0;
    let mut v_i_boxed_9151_: usize = 0;
    let mut v_res_9152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_9150_ = leanh::lean_unbox_usize(v_sz_9147_);
    leanh::lean_dec(v_sz_9147_);
    v_i_boxed_9151_ = leanh::lean_unbox_usize(v_i_9148_);
    leanh::lean_dec(v_i_9148_);
    v_res_9152_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_boxed_9150_, v_i_boxed_9151_, v_bs_9149_);
    return v_res_9152_;
}
pub unsafe fn l_Lean_MVarId_extractLets___lam__0(
    mut v___x_9153_: *mut leanh::LeanObject,
    mut v_mvarId_9154_: *mut leanh::LeanObject,
    mut v___x_9155_: *mut leanh::LeanObject,
    mut v_a_9156_: *mut leanh::LeanObject,
    mut v_fvarIds_9157_: *mut leanh::LeanObject,
    mut v_es_9158_: *mut leanh::LeanObject,
    mut v_givenNames_x27_9159_: *mut leanh::LeanObject,
    mut v___y_9160_: *mut leanh::LeanObject,
    mut v___y_9161_: *mut leanh::LeanObject,
    mut v___y_9162_: *mut leanh::LeanObject,
    mut v___y_9163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_9172_: usize = 0;
    let mut v___x_9173_: usize = 0;
    let mut v___x_9174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9175_: u8 = 0;
    let mut v___x_9176_: u8 = 0;
    let mut v___x_9177_: u8 = 0;
    let mut v___x_9178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9183_: u8 = 0;
    let mut v___x_9184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9190_: u8 = 0;
    let mut v_unused_9191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9195_: u8 = 0;
    let mut v___x_9197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9199_: u8 = 0;
    let mut v_a_9200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9203_: u8 = 0;
    let mut v___x_9205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9207_: u8 = 0;
    let mut v_a_9208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9211_: u8 = 0;
    let mut v___x_9213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9215_: u8 = 0;
    let mut v___y_9217_: u8 = 0;
    let mut v___x_9218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9222_: u8 = 0;
    let mut v___x_9224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9226_: u8 = 0;
    let mut v___x_9227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9228_: u8 = 0;
    let mut v___x_9229_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9165_ = leanh::lean_unsigned_to_nat(0);
                v___x_9166_ = lean_array_get_borrowed(v___x_9153_, v_es_9158_, v___x_9165_);
                v___x_9227_ = lean_array_get_size(v_fvarIds_9157_);
                v___x_9228_ = lean_nat_dec_eq(v___x_9227_, v___x_9165_);
                if v___x_9228_ == 0 {
                    v___y_9217_ = v___x_9228_;
                    state = 10;
                    continue;
                } else {
                    v___x_9229_ = lean_expr_eqv(v_a_9156_, v___x_9166_);
                    v___y_9217_ = v___x_9229_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_mvarId_9154_);
                v___x_9168_ = l_Lean_MVarId_getTag(
                    v_mvarId_9154_,
                    v___y_9160_,
                    v___y_9161_,
                    v___y_9162_,
                    v___y_9163_,
                );
                if leanh::lean_obj_tag(v___x_9168_) == 0 {
                    v_a_9169_ = leanh::lean_ctor_get(v___x_9168_, 0);
                    leanh::lean_inc(v_a_9169_);
                    leanh::lean_dec_ref_known(v___x_9168_, 1);
                    leanh::lean_inc(v___x_9166_);
                    v___x_9170_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                        v___x_9166_,
                        v_a_9169_,
                        v___y_9160_,
                        v___y_9161_,
                        v___y_9162_,
                        v___y_9163_,
                    );
                    if leanh::lean_obj_tag(v___x_9170_) == 0 {
                        v_a_9171_ = leanh::lean_ctor_get(v___x_9170_, 0);
                        leanh::lean_inc_n(v_a_9171_, 2);
                        leanh::lean_dec_ref_known(v___x_9170_, 1);
                        v_sz_9172_ = lean_array_size(v_fvarIds_9157_);
                        v___x_9173_ = 0usize;
                        leanh::lean_inc_ref(v_fvarIds_9157_);
                        v___x_9174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_9172_, v___x_9173_, v_fvarIds_9157_);
                        v___x_9175_ = 0;
                        v___x_9176_ = 1;
                        v___x_9177_ = 1;
                        v___x_9178_ = l_Lean_Meta_mkLetFVars(
                            v___x_9174_,
                            v_a_9171_,
                            v___x_9175_,
                            v___x_9176_,
                            v___x_9177_,
                            v___y_9160_,
                            v___y_9161_,
                            v___y_9162_,
                            v___y_9163_,
                        );
                        leanh::lean_dec_ref(v___x_9174_);
                        if leanh::lean_obj_tag(v___x_9178_) == 0 {
                            v_a_9179_ = leanh::lean_ctor_get(v___x_9178_, 0);
                            leanh::lean_inc(v_a_9179_);
                            leanh::lean_dec_ref_known(v___x_9178_, 1);
                            v___x_9180_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_9154_, v_a_9179_, v___y_9161_);
                            v_isSharedCheck_9190_ =
                                (!leanh::lean_is_exclusive(v___x_9180_)) as u8;
                            if v_isSharedCheck_9190_ == 0 {
                                v_unused_9191_ = leanh::lean_ctor_get(v___x_9180_, 0);
                                leanh::lean_dec(v_unused_9191_);
                                v___x_9182_ = v___x_9180_;
                                v_isShared_9183_ = v_isSharedCheck_9190_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_9180_);
                                v___x_9182_ = leanh::lean_box(0);
                                v_isShared_9183_ = v_isSharedCheck_9190_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_9171_);
                            leanh::lean_dec(v_givenNames_x27_9159_);
                            leanh::lean_dec_ref(v_fvarIds_9157_);
                            leanh::lean_dec(v_mvarId_9154_);
                            v_a_9192_ = leanh::lean_ctor_get(v___x_9178_, 0);
                            v_isSharedCheck_9199_ =
                                (!leanh::lean_is_exclusive(v___x_9178_)) as u8;
                            if v_isSharedCheck_9199_ == 0 {
                                v___x_9194_ = v___x_9178_;
                                v_isShared_9195_ = v_isSharedCheck_9199_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_9192_);
                                leanh::lean_dec(v___x_9178_);
                                v___x_9194_ = leanh::lean_box(0);
                                v_isShared_9195_ = v_isSharedCheck_9199_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_givenNames_x27_9159_);
                        leanh::lean_dec_ref(v_fvarIds_9157_);
                        leanh::lean_dec(v_mvarId_9154_);
                        v_a_9200_ = leanh::lean_ctor_get(v___x_9170_, 0);
                        v_isSharedCheck_9207_ =
                            (!leanh::lean_is_exclusive(v___x_9170_)) as u8;
                        if v_isSharedCheck_9207_ == 0 {
                            v___x_9202_ = v___x_9170_;
                            v_isShared_9203_ = v_isSharedCheck_9207_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9200_);
                            leanh::lean_dec(v___x_9170_);
                            v___x_9202_ = leanh::lean_box(0);
                            v_isShared_9203_ = v_isSharedCheck_9207_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_givenNames_x27_9159_);
                    leanh::lean_dec_ref(v_fvarIds_9157_);
                    leanh::lean_dec(v_mvarId_9154_);
                    v_a_9208_ = leanh::lean_ctor_get(v___x_9168_, 0);
                    v_isSharedCheck_9215_ = (!leanh::lean_is_exclusive(v___x_9168_)) as u8;
                    if v_isSharedCheck_9215_ == 0 {
                        v___x_9210_ = v___x_9168_;
                        v_isShared_9211_ = v_isSharedCheck_9215_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9208_);
                        leanh::lean_dec(v___x_9168_);
                        v___x_9210_ = leanh::lean_box(0);
                        v_isShared_9211_ = v_isSharedCheck_9215_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_9184_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_9184_, 0, v_fvarIds_9157_);
                leanh::lean_ctor_set(v___x_9184_, 1, v_givenNames_x27_9159_);
                v___x_9185_ = l_Lean_Expr_mvarId_x21(v_a_9171_);
                leanh::lean_dec(v_a_9171_);
                v___x_9186_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_9186_, 0, v___x_9184_);
                leanh::lean_ctor_set(v___x_9186_, 1, v___x_9185_);
                if v_isShared_9183_ == 0 {
                    leanh::lean_ctor_set(v___x_9182_, 0, v___x_9186_);
                    v___x_9188_ = v___x_9182_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9189_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9189_, 0, v___x_9186_);
                    v___x_9188_ = v_reuseFailAlloc_9189_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_9188_;
            }
            4 => {
                if v_isShared_9195_ == 0 {
                    v___x_9197_ = v___x_9194_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9198_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9198_, 0, v_a_9192_);
                    v___x_9197_ = v_reuseFailAlloc_9198_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_9197_;
            }
            6 => {
                if v_isShared_9203_ == 0 {
                    v___x_9205_ = v___x_9202_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_9206_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9206_, 0, v_a_9200_);
                    v___x_9205_ = v_reuseFailAlloc_9206_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_9205_;
            }
            8 => {
                if v_isShared_9211_ == 0 {
                    v___x_9213_ = v___x_9210_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_9214_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9214_, 0, v_a_9208_);
                    v___x_9213_ = v_reuseFailAlloc_9214_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_9213_;
            }
            10 => {
                if v___y_9217_ == 0 {
                    leanh::lean_dec(v___x_9155_);
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_mvarId_9154_);
                    v___x_9218_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(
                        v___x_9155_,
                        v_mvarId_9154_,
                        v___y_9160_,
                        v___y_9161_,
                        v___y_9162_,
                        v___y_9163_,
                    );
                    if leanh::lean_obj_tag(v___x_9218_) == 0 {
                        leanh::lean_dec_ref_known(v___x_9218_, 1);
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_givenNames_x27_9159_);
                        leanh::lean_dec_ref(v_fvarIds_9157_);
                        leanh::lean_dec(v_mvarId_9154_);
                        v_a_9219_ = leanh::lean_ctor_get(v___x_9218_, 0);
                        v_isSharedCheck_9226_ =
                            (!leanh::lean_is_exclusive(v___x_9218_)) as u8;
                        if v_isSharedCheck_9226_ == 0 {
                            v___x_9221_ = v___x_9218_;
                            v_isShared_9222_ = v_isSharedCheck_9226_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9219_);
                            leanh::lean_dec(v___x_9218_);
                            v___x_9221_ = leanh::lean_box(0);
                            v_isShared_9222_ = v_isSharedCheck_9226_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            11 => {
                if v_isShared_9222_ == 0 {
                    v___x_9224_ = v___x_9221_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_9225_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9225_, 0, v_a_9219_);
                    v___x_9224_ = v_reuseFailAlloc_9225_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_9224_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_extractLets___lam__0___boxed(
    mut v___x_9230_: *mut leanh::LeanObject,
    mut v_mvarId_9231_: *mut leanh::LeanObject,
    mut v___x_9232_: *mut leanh::LeanObject,
    mut v_a_9233_: *mut leanh::LeanObject,
    mut v_fvarIds_9234_: *mut leanh::LeanObject,
    mut v_es_9235_: *mut leanh::LeanObject,
    mut v_givenNames_x27_9236_: *mut leanh::LeanObject,
    mut v___y_9237_: *mut leanh::LeanObject,
    mut v___y_9238_: *mut leanh::LeanObject,
    mut v___y_9239_: *mut leanh::LeanObject,
    mut v___y_9240_: *mut leanh::LeanObject,
    mut v___y_9241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9242_ = l_Lean_MVarId_extractLets___lam__0(
        v___x_9230_,
        v_mvarId_9231_,
        v___x_9232_,
        v_a_9233_,
        v_fvarIds_9234_,
        v_es_9235_,
        v_givenNames_x27_9236_,
        v___y_9237_,
        v___y_9238_,
        v___y_9239_,
        v___y_9240_,
    );
    leanh::lean_dec(v___y_9240_);
    leanh::lean_dec_ref(v___y_9239_);
    leanh::lean_dec(v___y_9238_);
    leanh::lean_dec_ref(v___y_9237_);
    leanh::lean_dec_ref(v_es_9235_);
    leanh::lean_dec_ref(v_a_9233_);
    leanh::lean_dec_ref(v___x_9230_);
    return v_res_9242_;
}
pub unsafe fn l_Lean_MVarId_extractLets___lam__1(
    mut v_mvarId_9243_: *mut leanh::LeanObject,
    mut v___x_9244_: *mut leanh::LeanObject,
    mut v___x_9245_: *mut leanh::LeanObject,
    mut v_givenNames_9246_: *mut leanh::LeanObject,
    mut v_config_9247_: *mut leanh::LeanObject,
    mut v___y_9248_: *mut leanh::LeanObject,
    mut v___y_9249_: *mut leanh::LeanObject,
    mut v___y_9250_: *mut leanh::LeanObject,
    mut v___y_9251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9264_: u8 = 0;
    let mut v___x_9266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9268_: u8 = 0;
    let mut v_a_9269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9272_: u8 = 0;
    let mut v___x_9274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9276_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___x_9244_);
                leanh::lean_inc(v_mvarId_9243_);
                v___x_9253_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_9243_,
                    v___x_9244_,
                    v___y_9248_,
                    v___y_9249_,
                    v___y_9250_,
                    v___y_9251_,
                );
                if leanh::lean_obj_tag(v___x_9253_) == 0 {
                    leanh::lean_dec_ref_known(v___x_9253_, 1);
                    leanh::lean_inc(v_mvarId_9243_);
                    v___x_9254_ = l_Lean_MVarId_getType(
                        v_mvarId_9243_,
                        v___y_9248_,
                        v___y_9249_,
                        v___y_9250_,
                        v___y_9251_,
                    );
                    if leanh::lean_obj_tag(v___x_9254_) == 0 {
                        v_a_9255_ = leanh::lean_ctor_get(v___x_9254_, 0);
                        leanh::lean_inc_n(v_a_9255_, 2);
                        leanh::lean_dec_ref_known(v___x_9254_, 1);
                        v___f_9256_ = leanh::lean_alloc_closure(
                            l_Lean_MVarId_extractLets___lam__0___boxed as *mut core::ffi::c_void,
                            12,
                            4,
                        );
                        leanh::lean_closure_set(v___f_9256_, 0, v___x_9245_);
                        leanh::lean_closure_set(v___f_9256_, 1, v_mvarId_9243_);
                        leanh::lean_closure_set(v___f_9256_, 2, v___x_9244_);
                        leanh::lean_closure_set(v___f_9256_, 3, v_a_9255_);
                        v___x_9257_ = leanh::lean_unsigned_to_nat(1);
                        v___x_9258_ = lean_mk_empty_array_with_capacity(v___x_9257_);
                        v___x_9259_ = lean_array_push(v___x_9258_, v_a_9255_);
                        v___x_9260_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_9259_, v_givenNames_9246_, v___f_9256_, v_config_9247_, v___y_9248_, v___y_9249_, v___y_9250_, v___y_9251_);
                        return v___x_9260_;
                    } else {
                        leanh::lean_dec(v_givenNames_9246_);
                        leanh::lean_dec_ref(v___x_9245_);
                        leanh::lean_dec(v___x_9244_);
                        leanh::lean_dec(v_mvarId_9243_);
                        v_a_9261_ = leanh::lean_ctor_get(v___x_9254_, 0);
                        v_isSharedCheck_9268_ =
                            (!leanh::lean_is_exclusive(v___x_9254_)) as u8;
                        if v_isSharedCheck_9268_ == 0 {
                            v___x_9263_ = v___x_9254_;
                            v_isShared_9264_ = v_isSharedCheck_9268_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9261_);
                            leanh::lean_dec(v___x_9254_);
                            v___x_9263_ = leanh::lean_box(0);
                            v_isShared_9264_ = v_isSharedCheck_9268_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_givenNames_9246_);
                    leanh::lean_dec_ref(v___x_9245_);
                    leanh::lean_dec(v___x_9244_);
                    leanh::lean_dec(v_mvarId_9243_);
                    v_a_9269_ = leanh::lean_ctor_get(v___x_9253_, 0);
                    v_isSharedCheck_9276_ = (!leanh::lean_is_exclusive(v___x_9253_)) as u8;
                    if v_isSharedCheck_9276_ == 0 {
                        v___x_9271_ = v___x_9253_;
                        v_isShared_9272_ = v_isSharedCheck_9276_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9269_);
                        leanh::lean_dec(v___x_9253_);
                        v___x_9271_ = leanh::lean_box(0);
                        v_isShared_9272_ = v_isSharedCheck_9276_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9264_ == 0 {
                    v___x_9266_ = v___x_9263_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9267_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9267_, 0, v_a_9261_);
                    v___x_9266_ = v_reuseFailAlloc_9267_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9266_;
            }
            3 => {
                if v_isShared_9272_ == 0 {
                    v___x_9274_ = v___x_9271_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9275_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9275_, 0, v_a_9269_);
                    v___x_9274_ = v_reuseFailAlloc_9275_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_extractLets___lam__1___boxed(
    mut v_mvarId_9277_: *mut leanh::LeanObject,
    mut v___x_9278_: *mut leanh::LeanObject,
    mut v___x_9279_: *mut leanh::LeanObject,
    mut v_givenNames_9280_: *mut leanh::LeanObject,
    mut v_config_9281_: *mut leanh::LeanObject,
    mut v___y_9282_: *mut leanh::LeanObject,
    mut v___y_9283_: *mut leanh::LeanObject,
    mut v___y_9284_: *mut leanh::LeanObject,
    mut v___y_9285_: *mut leanh::LeanObject,
    mut v___y_9286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9287_ = l_Lean_MVarId_extractLets___lam__1(
        v_mvarId_9277_,
        v___x_9278_,
        v___x_9279_,
        v_givenNames_9280_,
        v_config_9281_,
        v___y_9282_,
        v___y_9283_,
        v___y_9284_,
        v___y_9285_,
    );
    leanh::lean_dec(v___y_9285_);
    leanh::lean_dec_ref(v___y_9284_);
    leanh::lean_dec(v___y_9283_);
    leanh::lean_dec_ref(v___y_9282_);
    leanh::lean_dec_ref(v_config_9281_);
    return v_res_9287_;
}
pub unsafe fn l_Lean_MVarId_extractLets(
    mut v_mvarId_9291_: *mut leanh::LeanObject,
    mut v_givenNames_9292_: *mut leanh::LeanObject,
    mut v_config_9293_: *mut leanh::LeanObject,
    mut v_a_9294_: *mut leanh::LeanObject,
    mut v_a_9295_: *mut leanh::LeanObject,
    mut v_a_9296_: *mut leanh::LeanObject,
    mut v_a_9297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9299_ = l_Lean_instInhabitedExpr;
    v___x_9300_ = l_Lean_MVarId_extractLets___closed__1;
    leanh::lean_inc(v_mvarId_9291_);
    v___f_9301_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_extractLets___lam__1___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    leanh::lean_closure_set(v___f_9301_, 0, v_mvarId_9291_);
    leanh::lean_closure_set(v___f_9301_, 1, v___x_9300_);
    leanh::lean_closure_set(v___f_9301_, 2, v___x_9299_);
    leanh::lean_closure_set(v___f_9301_, 3, v_givenNames_9292_);
    leanh::lean_closure_set(v___f_9301_, 4, v_config_9293_);
    v___x_9302_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(
        v_mvarId_9291_,
        v___f_9301_,
        v_a_9294_,
        v_a_9295_,
        v_a_9296_,
        v_a_9297_,
    );
    return v___x_9302_;
}
pub unsafe fn l_Lean_MVarId_extractLets___boxed(
    mut v_mvarId_9303_: *mut leanh::LeanObject,
    mut v_givenNames_9304_: *mut leanh::LeanObject,
    mut v_config_9305_: *mut leanh::LeanObject,
    mut v_a_9306_: *mut leanh::LeanObject,
    mut v_a_9307_: *mut leanh::LeanObject,
    mut v_a_9308_: *mut leanh::LeanObject,
    mut v_a_9309_: *mut leanh::LeanObject,
    mut v_a_9310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9311_ = l_Lean_MVarId_extractLets(
        v_mvarId_9303_,
        v_givenNames_9304_,
        v_config_9305_,
        v_a_9306_,
        v_a_9307_,
        v_a_9308_,
        v_a_9309_,
    );
    leanh::lean_dec(v_a_9309_);
    leanh::lean_dec_ref(v_a_9308_);
    leanh::lean_dec(v_a_9307_);
    leanh::lean_dec_ref(v_a_9306_);
    return v_res_9311_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(
    mut v_mvarId_9312_: *mut leanh::LeanObject,
    mut v_val_9313_: *mut leanh::LeanObject,
    mut v___y_9314_: *mut leanh::LeanObject,
    mut v___y_9315_: *mut leanh::LeanObject,
    mut v___y_9316_: *mut leanh::LeanObject,
    mut v___y_9317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9319_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(
        v_mvarId_9312_,
        v_val_9313_,
        v___y_9315_,
    );
    return v___x_9319_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___boxed(
    mut v_mvarId_9320_: *mut leanh::LeanObject,
    mut v_val_9321_: *mut leanh::LeanObject,
    mut v___y_9322_: *mut leanh::LeanObject,
    mut v___y_9323_: *mut leanh::LeanObject,
    mut v___y_9324_: *mut leanh::LeanObject,
    mut v___y_9325_: *mut leanh::LeanObject,
    mut v___y_9326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9327_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1(
        v_mvarId_9320_,
        v_val_9321_,
        v___y_9322_,
        v___y_9323_,
        v___y_9324_,
        v___y_9325_,
    );
    leanh::lean_dec(v___y_9325_);
    leanh::lean_dec_ref(v___y_9324_);
    leanh::lean_dec(v___y_9323_);
    leanh::lean_dec_ref(v___y_9322_);
    return v_res_9327_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1(
    mut v_00_u03b2_9328_: *mut leanh::LeanObject,
    mut v_x_9329_: *mut leanh::LeanObject,
    mut v_x_9330_: *mut leanh::LeanObject,
    mut v_x_9331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9332_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1___redArg(v_x_9329_, v_x_9330_, v_x_9331_);
    return v___x_9332_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(
    mut v_00_u03b2_9333_: *mut leanh::LeanObject,
    mut v_x_9334_: *mut leanh::LeanObject,
    mut v_x_9335_: usize,
    mut v_x_9336_: usize,
    mut v_x_9337_: *mut leanh::LeanObject,
    mut v_x_9338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9339_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___redArg(v_x_9334_, v_x_9335_, v_x_9336_, v_x_9337_, v_x_9338_);
    return v___x_9339_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4___boxed(
    mut v_00_u03b2_9340_: *mut leanh::LeanObject,
    mut v_x_9341_: *mut leanh::LeanObject,
    mut v_x_9342_: *mut leanh::LeanObject,
    mut v_x_9343_: *mut leanh::LeanObject,
    mut v_x_9344_: *mut leanh::LeanObject,
    mut v_x_9345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2828__boxed_9346_: usize = 0;
    let mut v_x_2829__boxed_9347_: usize = 0;
    let mut v_res_9348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2828__boxed_9346_ = leanh::lean_unbox_usize(v_x_9342_);
    leanh::lean_dec(v_x_9342_);
    v_x_2829__boxed_9347_ = leanh::lean_unbox_usize(v_x_9343_);
    leanh::lean_dec(v_x_9343_);
    v_res_9348_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4(v_00_u03b2_9340_, v_x_9341_, v_x_2828__boxed_9346_, v_x_2829__boxed_9347_, v_x_9344_, v_x_9345_);
    return v_res_9348_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5(
    mut v_00_u03b2_9349_: *mut leanh::LeanObject,
    mut v_n_9350_: *mut leanh::LeanObject,
    mut v_k_9351_: *mut leanh::LeanObject,
    mut v_v_9352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9353_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5___redArg(v_n_9350_, v_k_9351_, v_v_9352_);
    return v___x_9353_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(
    mut v_00_u03b2_9354_: *mut leanh::LeanObject,
    mut v_depth_9355_: usize,
    mut v_keys_9356_: *mut leanh::LeanObject,
    mut v_vals_9357_: *mut leanh::LeanObject,
    mut v_heq_9358_: *mut leanh::LeanObject,
    mut v_i_9359_: *mut leanh::LeanObject,
    mut v_entries_9360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9361_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___redArg(v_depth_9355_, v_keys_9356_, v_vals_9357_, v_i_9359_, v_entries_9360_);
    return v___x_9361_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6___boxed(
    mut v_00_u03b2_9362_: *mut leanh::LeanObject,
    mut v_depth_9363_: *mut leanh::LeanObject,
    mut v_keys_9364_: *mut leanh::LeanObject,
    mut v_vals_9365_: *mut leanh::LeanObject,
    mut v_heq_9366_: *mut leanh::LeanObject,
    mut v_i_9367_: *mut leanh::LeanObject,
    mut v_entries_9368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_9369_: usize = 0;
    let mut v_res_9370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_9369_ = leanh::lean_unbox_usize(v_depth_9363_);
    leanh::lean_dec(v_depth_9363_);
    v_res_9370_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__6(v_00_u03b2_9362_, v_depth_boxed_9369_, v_keys_9364_, v_vals_9365_, v_heq_9366_, v_i_9367_, v_entries_9368_);
    leanh::lean_dec_ref(v_vals_9365_);
    leanh::lean_dec_ref(v_keys_9364_);
    return v_res_9370_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6(
    mut v_00_u03b2_9371_: *mut leanh::LeanObject,
    mut v_x_9372_: *mut leanh::LeanObject,
    mut v_x_9373_: *mut leanh::LeanObject,
    mut v_x_9374_: *mut leanh::LeanObject,
    mut v_x_9375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9376_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1_spec__1_spec__4_spec__5_spec__6___redArg(v_x_9372_, v_x_9373_, v_x_9374_, v_x_9375_);
    return v___x_9376_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(
    mut v_sz_9377_: usize,
    mut v_i_9378_: usize,
    mut v_bs_9379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9380_: u8 = 0;
    let mut v_v_9381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_9383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9385_: usize = 0;
    let mut v___x_9386_: usize = 0;
    let mut v___x_9387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9380_ = lean_usize_dec_lt(v_i_9378_, v_sz_9377_);
                if v___x_9380_ == 0 {
                    return v_bs_9379_;
                } else {
                    v_v_9381_ = lean_array_uget(v_bs_9379_, v_i_9378_);
                    v___x_9382_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_9383_ = lean_array_uset(v_bs_9379_, v_i_9378_, v___x_9382_);
                    v___x_9384_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_9384_, 0, v_v_9381_);
                    v___x_9385_ = 1usize;
                    v___x_9386_ = lean_usize_add(v_i_9378_, v___x_9385_);
                    v___x_9387_ = lean_array_uset(v_bs_x27_9383_, v_i_9378_, v___x_9384_);
                    v_i_9378_ = v___x_9386_;
                    v_bs_9379_ = v___x_9387_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0___boxed(
    mut v_sz_9389_: *mut leanh::LeanObject,
    mut v_i_9390_: *mut leanh::LeanObject,
    mut v_bs_9391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_9392_: usize = 0;
    let mut v_i_boxed_9393_: usize = 0;
    let mut v_res_9394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_9392_ = leanh::lean_unbox_usize(v_sz_9389_);
    leanh::lean_dec(v_sz_9389_);
    v_i_boxed_9393_ = leanh::lean_unbox_usize(v_i_9390_);
    leanh::lean_dec(v_i_9390_);
    v_res_9394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_boxed_9392_, v_i_boxed_9393_, v_bs_9391_);
    return v_res_9394_;
}
pub unsafe fn l_Lean_MVarId_extractLetsLocalDecl___lam__0(
    mut v_mvarId_9395_: *mut leanh::LeanObject,
    mut v_fvars_9396_: *mut leanh::LeanObject,
    mut v_fvarIds_9397_: *mut leanh::LeanObject,
    mut v_givenNames_x27_9398_: *mut leanh::LeanObject,
    mut v_targetNew_9399_: *mut leanh::LeanObject,
    mut v___y_9400_: *mut leanh::LeanObject,
    mut v___y_9401_: *mut leanh::LeanObject,
    mut v___y_9402_: *mut leanh::LeanObject,
    mut v___y_9403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_9409_: usize = 0;
    let mut v___x_9410_: usize = 0;
    let mut v___x_9411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9412_: u8 = 0;
    let mut v___x_9413_: u8 = 0;
    let mut v___x_9414_: u8 = 0;
    let mut v___x_9415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9420_: u8 = 0;
    let mut v___x_9421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_9422_: usize = 0;
    let mut v___x_9423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9430_: u8 = 0;
    let mut v_unused_9431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9435_: u8 = 0;
    let mut v___x_9437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9439_: u8 = 0;
    let mut v_a_9440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9443_: u8 = 0;
    let mut v___x_9445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9447_: u8 = 0;
    let mut v_a_9448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9451_: u8 = 0;
    let mut v___x_9453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_9395_);
                v___x_9405_ = l_Lean_MVarId_getTag(
                    v_mvarId_9395_,
                    v___y_9400_,
                    v___y_9401_,
                    v___y_9402_,
                    v___y_9403_,
                );
                if leanh::lean_obj_tag(v___x_9405_) == 0 {
                    v_a_9406_ = leanh::lean_ctor_get(v___x_9405_, 0);
                    leanh::lean_inc(v_a_9406_);
                    leanh::lean_dec_ref_known(v___x_9405_, 1);
                    v___x_9407_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                        v_targetNew_9399_,
                        v_a_9406_,
                        v___y_9400_,
                        v___y_9401_,
                        v___y_9402_,
                        v___y_9403_,
                    );
                    if leanh::lean_obj_tag(v___x_9407_) == 0 {
                        v_a_9408_ = leanh::lean_ctor_get(v___x_9407_, 0);
                        leanh::lean_inc_n(v_a_9408_, 2);
                        leanh::lean_dec_ref_known(v___x_9407_, 1);
                        v_sz_9409_ = lean_array_size(v_fvarIds_9397_);
                        v___x_9410_ = 0usize;
                        leanh::lean_inc_ref(v_fvarIds_9397_);
                        v___x_9411_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLets_spec__0(v_sz_9409_, v___x_9410_, v_fvarIds_9397_);
                        v___x_9412_ = 0;
                        v___x_9413_ = 1;
                        v___x_9414_ = 1;
                        v___x_9415_ = l_Lean_Meta_mkLetFVars(
                            v___x_9411_,
                            v_a_9408_,
                            v___x_9412_,
                            v___x_9413_,
                            v___x_9414_,
                            v___y_9400_,
                            v___y_9401_,
                            v___y_9402_,
                            v___y_9403_,
                        );
                        leanh::lean_dec_ref(v___x_9411_);
                        if leanh::lean_obj_tag(v___x_9415_) == 0 {
                            v_a_9416_ = leanh::lean_ctor_get(v___x_9415_, 0);
                            leanh::lean_inc(v_a_9416_);
                            leanh::lean_dec_ref_known(v___x_9415_, 1);
                            v___x_9417_ = l_Lean_MVarId_assign___at___00Lean_MVarId_extractLets_spec__1___redArg(v_mvarId_9395_, v_a_9416_, v___y_9401_);
                            v_isSharedCheck_9430_ =
                                (!leanh::lean_is_exclusive(v___x_9417_)) as u8;
                            if v_isSharedCheck_9430_ == 0 {
                                v_unused_9431_ = leanh::lean_ctor_get(v___x_9417_, 0);
                                leanh::lean_dec(v_unused_9431_);
                                v___x_9419_ = v___x_9417_;
                                v_isShared_9420_ = v_isSharedCheck_9430_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_9417_);
                                v___x_9419_ = leanh::lean_box(0);
                                v_isShared_9420_ = v_isSharedCheck_9430_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_9408_);
                            leanh::lean_dec(v_givenNames_x27_9398_);
                            leanh::lean_dec_ref(v_fvarIds_9397_);
                            leanh::lean_dec_ref(v_fvars_9396_);
                            leanh::lean_dec(v_mvarId_9395_);
                            v_a_9432_ = leanh::lean_ctor_get(v___x_9415_, 0);
                            v_isSharedCheck_9439_ =
                                (!leanh::lean_is_exclusive(v___x_9415_)) as u8;
                            if v_isSharedCheck_9439_ == 0 {
                                v___x_9434_ = v___x_9415_;
                                v_isShared_9435_ = v_isSharedCheck_9439_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_9432_);
                                leanh::lean_dec(v___x_9415_);
                                v___x_9434_ = leanh::lean_box(0);
                                v_isShared_9435_ = v_isSharedCheck_9439_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_givenNames_x27_9398_);
                        leanh::lean_dec_ref(v_fvarIds_9397_);
                        leanh::lean_dec_ref(v_fvars_9396_);
                        leanh::lean_dec(v_mvarId_9395_);
                        v_a_9440_ = leanh::lean_ctor_get(v___x_9407_, 0);
                        v_isSharedCheck_9447_ =
                            (!leanh::lean_is_exclusive(v___x_9407_)) as u8;
                        if v_isSharedCheck_9447_ == 0 {
                            v___x_9442_ = v___x_9407_;
                            v_isShared_9443_ = v_isSharedCheck_9447_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9440_);
                            leanh::lean_dec(v___x_9407_);
                            v___x_9442_ = leanh::lean_box(0);
                            v_isShared_9443_ = v_isSharedCheck_9447_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_targetNew_9399_);
                    leanh::lean_dec(v_givenNames_x27_9398_);
                    leanh::lean_dec_ref(v_fvarIds_9397_);
                    leanh::lean_dec_ref(v_fvars_9396_);
                    leanh::lean_dec(v_mvarId_9395_);
                    v_a_9448_ = leanh::lean_ctor_get(v___x_9405_, 0);
                    v_isSharedCheck_9455_ = (!leanh::lean_is_exclusive(v___x_9405_)) as u8;
                    if v_isSharedCheck_9455_ == 0 {
                        v___x_9450_ = v___x_9405_;
                        v_isShared_9451_ = v_isSharedCheck_9455_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9448_);
                        leanh::lean_dec(v___x_9405_);
                        v___x_9450_ = leanh::lean_box(0);
                        v_isShared_9451_ = v_isSharedCheck_9455_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9421_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_9421_, 0, v_fvarIds_9397_);
                leanh::lean_ctor_set(v___x_9421_, 1, v_givenNames_x27_9398_);
                v_sz_9422_ = lean_array_size(v_fvars_9396_);
                v___x_9423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_9422_, v___x_9410_, v_fvars_9396_);
                v___x_9424_ = l_Lean_Expr_mvarId_x21(v_a_9408_);
                leanh::lean_dec(v_a_9408_);
                v___x_9425_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_9425_, 0, v___x_9423_);
                leanh::lean_ctor_set(v___x_9425_, 1, v___x_9424_);
                v___x_9426_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_9426_, 0, v___x_9421_);
                leanh::lean_ctor_set(v___x_9426_, 1, v___x_9425_);
                if v_isShared_9420_ == 0 {
                    leanh::lean_ctor_set(v___x_9419_, 0, v___x_9426_);
                    v___x_9428_ = v___x_9419_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9429_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9429_, 0, v___x_9426_);
                    v___x_9428_ = v_reuseFailAlloc_9429_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9428_;
            }
            3 => {
                if v_isShared_9435_ == 0 {
                    v___x_9437_ = v___x_9434_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9438_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9438_, 0, v_a_9432_);
                    v___x_9437_ = v_reuseFailAlloc_9438_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9437_;
            }
            5 => {
                if v_isShared_9443_ == 0 {
                    v___x_9445_ = v___x_9442_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_9446_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9446_, 0, v_a_9440_);
                    v___x_9445_ = v_reuseFailAlloc_9446_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_9445_;
            }
            7 => {
                if v_isShared_9451_ == 0 {
                    v___x_9453_ = v___x_9450_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_9454_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9454_, 0, v_a_9448_);
                    v___x_9453_ = v_reuseFailAlloc_9454_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_9453_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed(
    mut v_mvarId_9456_: *mut leanh::LeanObject,
    mut v_fvars_9457_: *mut leanh::LeanObject,
    mut v_fvarIds_9458_: *mut leanh::LeanObject,
    mut v_givenNames_x27_9459_: *mut leanh::LeanObject,
    mut v_targetNew_9460_: *mut leanh::LeanObject,
    mut v___y_9461_: *mut leanh::LeanObject,
    mut v___y_9462_: *mut leanh::LeanObject,
    mut v___y_9463_: *mut leanh::LeanObject,
    mut v___y_9464_: *mut leanh::LeanObject,
    mut v___y_9465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9466_ = l_Lean_MVarId_extractLetsLocalDecl___lam__0(
        v_mvarId_9456_,
        v_fvars_9457_,
        v_fvarIds_9458_,
        v_givenNames_x27_9459_,
        v_targetNew_9460_,
        v___y_9461_,
        v___y_9462_,
        v___y_9463_,
        v___y_9464_,
    );
    leanh::lean_dec(v___y_9464_);
    leanh::lean_dec_ref(v___y_9463_);
    leanh::lean_dec(v___y_9462_);
    leanh::lean_dec_ref(v___y_9461_);
    return v_res_9466_;
}
pub unsafe fn l_Lean_MVarId_extractLetsLocalDecl___lam__1(
    mut v___x_9467_: *mut leanh::LeanObject,
    mut v_binderName_9468_: *mut leanh::LeanObject,
    mut v_body_9469_: *mut leanh::LeanObject,
    mut v_binderInfo_9470_: u8,
    mut v___f_9471_: *mut leanh::LeanObject,
    mut v___x_9472_: *mut leanh::LeanObject,
    mut v_mvarId_9473_: *mut leanh::LeanObject,
    mut v_binderType_9474_: *mut leanh::LeanObject,
    mut v_fvarIds_9475_: *mut leanh::LeanObject,
    mut v_es_9476_: *mut leanh::LeanObject,
    mut v_givenNames_x27_9477_: *mut leanh::LeanObject,
    mut v___y_9478_: *mut leanh::LeanObject,
    mut v___y_9479_: *mut leanh::LeanObject,
    mut v___y_9480_: *mut leanh::LeanObject,
    mut v___y_9481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9489_: u8 = 0;
    let mut v___x_9490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9494_: u8 = 0;
    let mut v___x_9496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9498_: u8 = 0;
    let mut v___x_9499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9500_: u8 = 0;
    let mut v___x_9501_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9483_ = leanh::lean_unsigned_to_nat(0);
                v___x_9484_ = lean_array_get_borrowed(v___x_9467_, v_es_9476_, v___x_9483_);
                v___x_9499_ = lean_array_get_size(v_fvarIds_9475_);
                v___x_9500_ = lean_nat_dec_eq(v___x_9499_, v___x_9483_);
                if v___x_9500_ == 0 {
                    v___y_9489_ = v___x_9500_;
                    state = 2;
                    continue;
                } else {
                    v___x_9501_ = lean_expr_eqv(v_binderType_9474_, v___x_9484_);
                    v___y_9489_ = v___x_9501_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v___x_9484_);
                v___x_9486_ = l_Lean_Expr_forallE___override(
                    v_binderName_9468_,
                    v___x_9484_,
                    v_body_9469_,
                    v_binderInfo_9470_,
                );
                leanh::lean_inc(v___y_9481_);
                leanh::lean_inc_ref(v___y_9480_);
                leanh::lean_inc(v___y_9479_);
                leanh::lean_inc_ref(v___y_9478_);
                v___x_9487_ = leanh::lean_apply_8(
                    v___f_9471_,
                    v_fvarIds_9475_,
                    v_givenNames_x27_9477_,
                    v___x_9486_,
                    v___y_9478_,
                    v___y_9479_,
                    v___y_9480_,
                    v___y_9481_,
                    leanh::lean_box(0),
                );
                return v___x_9487_;
            }
            2 => {
                if v___y_9489_ == 0 {
                    leanh::lean_dec(v_mvarId_9473_);
                    leanh::lean_dec(v___x_9472_);
                    state = 1;
                    continue;
                } else {
                    v___x_9490_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(
                        v___x_9472_,
                        v_mvarId_9473_,
                        v___y_9478_,
                        v___y_9479_,
                        v___y_9480_,
                        v___y_9481_,
                    );
                    if leanh::lean_obj_tag(v___x_9490_) == 0 {
                        leanh::lean_dec_ref_known(v___x_9490_, 1);
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_givenNames_x27_9477_);
                        leanh::lean_dec_ref(v_fvarIds_9475_);
                        leanh::lean_dec_ref(v___f_9471_);
                        leanh::lean_dec_ref(v_body_9469_);
                        leanh::lean_dec(v_binderName_9468_);
                        v_a_9491_ = leanh::lean_ctor_get(v___x_9490_, 0);
                        v_isSharedCheck_9498_ =
                            (!leanh::lean_is_exclusive(v___x_9490_)) as u8;
                        if v_isSharedCheck_9498_ == 0 {
                            v___x_9493_ = v___x_9490_;
                            v_isShared_9494_ = v_isSharedCheck_9498_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9491_);
                            leanh::lean_dec(v___x_9490_);
                            v___x_9493_ = leanh::lean_box(0);
                            v_isShared_9494_ = v_isSharedCheck_9498_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_9494_ == 0 {
                    v___x_9496_ = v___x_9493_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9497_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9497_, 0, v_a_9491_);
                    v___x_9496_ = v_reuseFailAlloc_9497_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9496_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed(
    mut v___x_9502_: *mut leanh::LeanObject,
    mut v_binderName_9503_: *mut leanh::LeanObject,
    mut v_body_9504_: *mut leanh::LeanObject,
    mut v_binderInfo_9505_: *mut leanh::LeanObject,
    mut v___f_9506_: *mut leanh::LeanObject,
    mut v___x_9507_: *mut leanh::LeanObject,
    mut v_mvarId_9508_: *mut leanh::LeanObject,
    mut v_binderType_9509_: *mut leanh::LeanObject,
    mut v_fvarIds_9510_: *mut leanh::LeanObject,
    mut v_es_9511_: *mut leanh::LeanObject,
    mut v_givenNames_x27_9512_: *mut leanh::LeanObject,
    mut v___y_9513_: *mut leanh::LeanObject,
    mut v___y_9514_: *mut leanh::LeanObject,
    mut v___y_9515_: *mut leanh::LeanObject,
    mut v___y_9516_: *mut leanh::LeanObject,
    mut v___y_9517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderInfo_1854__boxed_9518_: u8 = 0;
    let mut v_res_9519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_1854__boxed_9518_ = (leanh::lean_unbox(v_binderInfo_9505_) as u8);
    v_res_9519_ = l_Lean_MVarId_extractLetsLocalDecl___lam__1(
        v___x_9502_,
        v_binderName_9503_,
        v_body_9504_,
        v_binderInfo_1854__boxed_9518_,
        v___f_9506_,
        v___x_9507_,
        v_mvarId_9508_,
        v_binderType_9509_,
        v_fvarIds_9510_,
        v_es_9511_,
        v_givenNames_x27_9512_,
        v___y_9513_,
        v___y_9514_,
        v___y_9515_,
        v___y_9516_,
    );
    leanh::lean_dec(v___y_9516_);
    leanh::lean_dec_ref(v___y_9515_);
    leanh::lean_dec(v___y_9514_);
    leanh::lean_dec_ref(v___y_9513_);
    leanh::lean_dec_ref(v_es_9511_);
    leanh::lean_dec_ref(v_binderType_9509_);
    leanh::lean_dec_ref(v___x_9502_);
    return v_res_9519_;
}
pub unsafe fn l_Lean_MVarId_extractLetsLocalDecl___lam__2(
    mut v___x_9520_: *mut leanh::LeanObject,
    mut v_declName_9521_: *mut leanh::LeanObject,
    mut v_body_9522_: *mut leanh::LeanObject,
    mut v_nondep_9523_: u8,
    mut v___f_9524_: *mut leanh::LeanObject,
    mut v_value_9525_: *mut leanh::LeanObject,
    mut v___x_9526_: *mut leanh::LeanObject,
    mut v_mvarId_9527_: *mut leanh::LeanObject,
    mut v_type_9528_: *mut leanh::LeanObject,
    mut v_fvarIds_9529_: *mut leanh::LeanObject,
    mut v_es_9530_: *mut leanh::LeanObject,
    mut v_givenNames_x27_9531_: *mut leanh::LeanObject,
    mut v___y_9532_: *mut leanh::LeanObject,
    mut v___y_9533_: *mut leanh::LeanObject,
    mut v___y_9534_: *mut leanh::LeanObject,
    mut v___y_9535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9545_: u8 = 0;
    let mut v___x_9546_: u8 = 0;
    let mut v___x_9547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9551_: u8 = 0;
    let mut v___x_9553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9555_: u8 = 0;
    let mut v___x_9556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9557_: u8 = 0;
    let mut v___x_9558_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9537_ = leanh::lean_unsigned_to_nat(0);
                v___x_9538_ = lean_array_get_borrowed(v___x_9520_, v_es_9530_, v___x_9537_);
                v___x_9539_ = leanh::lean_unsigned_to_nat(1);
                v___x_9540_ = lean_array_get_borrowed(v___x_9520_, v_es_9530_, v___x_9539_);
                v___x_9556_ = lean_array_get_size(v_fvarIds_9529_);
                v___x_9557_ = lean_nat_dec_eq(v___x_9556_, v___x_9537_);
                if v___x_9557_ == 0 {
                    v___y_9545_ = v___x_9557_;
                    state = 2;
                    continue;
                } else {
                    v___x_9558_ = lean_expr_eqv(v_type_9528_, v___x_9538_);
                    v___y_9545_ = v___x_9558_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v___x_9540_);
                leanh::lean_inc(v___x_9538_);
                v___x_9542_ = l_Lean_Expr_letE___override(
                    v_declName_9521_,
                    v___x_9538_,
                    v___x_9540_,
                    v_body_9522_,
                    v_nondep_9523_,
                );
                leanh::lean_inc(v___y_9535_);
                leanh::lean_inc_ref(v___y_9534_);
                leanh::lean_inc(v___y_9533_);
                leanh::lean_inc_ref(v___y_9532_);
                v___x_9543_ = leanh::lean_apply_8(
                    v___f_9524_,
                    v_fvarIds_9529_,
                    v_givenNames_x27_9531_,
                    v___x_9542_,
                    v___y_9532_,
                    v___y_9533_,
                    v___y_9534_,
                    v___y_9535_,
                    leanh::lean_box(0),
                );
                return v___x_9543_;
            }
            2 => {
                if v___y_9545_ == 0 {
                    leanh::lean_dec(v_mvarId_9527_);
                    leanh::lean_dec(v___x_9526_);
                    state = 1;
                    continue;
                } else {
                    v___x_9546_ = lean_expr_eqv(v_value_9525_, v___x_9540_);
                    if v___x_9546_ == 0 {
                        leanh::lean_dec(v_mvarId_9527_);
                        leanh::lean_dec(v___x_9526_);
                        state = 1;
                        continue;
                    } else {
                        v___x_9547_ =
                            l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(
                                v___x_9526_,
                                v_mvarId_9527_,
                                v___y_9532_,
                                v___y_9533_,
                                v___y_9534_,
                                v___y_9535_,
                            );
                        if leanh::lean_obj_tag(v___x_9547_) == 0 {
                            leanh::lean_dec_ref_known(v___x_9547_, 1);
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_givenNames_x27_9531_);
                            leanh::lean_dec_ref(v_fvarIds_9529_);
                            leanh::lean_dec_ref(v___f_9524_);
                            leanh::lean_dec_ref(v_body_9522_);
                            leanh::lean_dec(v_declName_9521_);
                            v_a_9548_ = leanh::lean_ctor_get(v___x_9547_, 0);
                            v_isSharedCheck_9555_ =
                                (!leanh::lean_is_exclusive(v___x_9547_)) as u8;
                            if v_isSharedCheck_9555_ == 0 {
                                v___x_9550_ = v___x_9547_;
                                v_isShared_9551_ = v_isSharedCheck_9555_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_9548_);
                                leanh::lean_dec(v___x_9547_);
                                v___x_9550_ = leanh::lean_box(0);
                                v_isShared_9551_ = v_isSharedCheck_9555_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                if v_isShared_9551_ == 0 {
                    v___x_9553_ = v___x_9550_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9554_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9554_, 0, v_a_9548_);
                    v___x_9553_ = v_reuseFailAlloc_9554_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9553_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9559_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_declName_9560_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_body_9561_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_nondep_9562_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___f_9563_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_value_9564_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_9565_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_mvarId_9566_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_type_9567_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_fvarIds_9568_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_es_9569_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_givenNames_x27_9570_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_9571_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_9572_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_9573_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_9574_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_9575_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_nondep_1929__boxed_9576_: u8 = 0;
    let mut v_res_9577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_1929__boxed_9576_ = (leanh::lean_unbox(v_nondep_9562_) as u8);
    v_res_9577_ = l_Lean_MVarId_extractLetsLocalDecl___lam__2(
        v___x_9559_,
        v_declName_9560_,
        v_body_9561_,
        v_nondep_1929__boxed_9576_,
        v___f_9563_,
        v_value_9564_,
        v___x_9565_,
        v_mvarId_9566_,
        v_type_9567_,
        v_fvarIds_9568_,
        v_es_9569_,
        v_givenNames_x27_9570_,
        v___y_9571_,
        v___y_9572_,
        v___y_9573_,
        v___y_9574_,
    );
    leanh::lean_dec(v___y_9574_);
    leanh::lean_dec_ref(v___y_9573_);
    leanh::lean_dec(v___y_9572_);
    leanh::lean_dec_ref(v___y_9571_);
    leanh::lean_dec_ref(v_es_9569_);
    leanh::lean_dec_ref(v_type_9567_);
    leanh::lean_dec_ref(v_value_9564_);
    leanh::lean_dec_ref(v___x_9559_);
    return v_res_9577_;
}
pub unsafe fn _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_9581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9581_ = l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__1;
    v___x_9582_ = l_Lean_MessageData_ofFormat(v___x_9581_);
    return v___x_9582_;
}
pub unsafe fn _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_9583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9583_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2_once),
        _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__2,
    );
    v___x_9584_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_9584_, 0, v___x_9583_);
    return v___x_9584_;
}
pub unsafe fn l_Lean_MVarId_extractLetsLocalDecl___lam__3(
    mut v_mvarId_9585_: *mut leanh::LeanObject,
    mut v___x_9586_: *mut leanh::LeanObject,
    mut v___f_9587_: *mut leanh::LeanObject,
    mut v___x_9588_: *mut leanh::LeanObject,
    mut v_givenNames_9589_: *mut leanh::LeanObject,
    mut v_config_9590_: *mut leanh::LeanObject,
    mut v___y_9591_: *mut leanh::LeanObject,
    mut v___y_9592_: *mut leanh::LeanObject,
    mut v___y_9593_: *mut leanh::LeanObject,
    mut v___y_9594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_9598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_9599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_9600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_9601_: u8 = 0;
    let mut v___x_9602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_9608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_9609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_9610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_9611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_9612_: u8 = 0;
    let mut v___x_9613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9625_: u8 = 0;
    let mut v___x_9627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9629_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_9585_);
                v___x_9596_ = l_Lean_MVarId_getType(
                    v_mvarId_9585_,
                    v___y_9591_,
                    v___y_9592_,
                    v___y_9593_,
                    v___y_9594_,
                );
                if leanh::lean_obj_tag(v___x_9596_) == 0 {
                    v_a_9597_ = leanh::lean_ctor_get(v___x_9596_, 0);
                    leanh::lean_inc(v_a_9597_);
                    leanh::lean_dec_ref_known(v___x_9596_, 1);
                    match leanh::lean_obj_tag(v_a_9597_) {
                        7 => {
                            v_binderName_9598_ = leanh::lean_ctor_get(v_a_9597_, 0);
                            leanh::lean_inc(v_binderName_9598_);
                            v_binderType_9599_ = leanh::lean_ctor_get(v_a_9597_, 1);
                            leanh::lean_inc_ref_n(v_binderType_9599_, 2);
                            v_body_9600_ = leanh::lean_ctor_get(v_a_9597_, 2);
                            leanh::lean_inc_ref(v_body_9600_);
                            v_binderInfo_9601_ = leanh::lean_ctor_get_uint8(
                                v_a_9597_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            leanh::lean_dec_ref_known(v_a_9597_, 3);
                            v___x_9602_ = leanh::lean_box((v_binderInfo_9601_) as usize);
                            v___f_9603_ = leanh::lean_alloc_closure(
                                l_Lean_MVarId_extractLetsLocalDecl___lam__1___boxed
                                    as *mut core::ffi::c_void,
                                16,
                                8,
                            );
                            leanh::lean_closure_set(v___f_9603_, 0, v___x_9586_);
                            leanh::lean_closure_set(v___f_9603_, 1, v_binderName_9598_);
                            leanh::lean_closure_set(v___f_9603_, 2, v_body_9600_);
                            leanh::lean_closure_set(v___f_9603_, 3, v___x_9602_);
                            leanh::lean_closure_set(v___f_9603_, 4, v___f_9587_);
                            leanh::lean_closure_set(v___f_9603_, 5, v___x_9588_);
                            leanh::lean_closure_set(v___f_9603_, 6, v_mvarId_9585_);
                            leanh::lean_closure_set(v___f_9603_, 7, v_binderType_9599_);
                            v___x_9604_ = leanh::lean_unsigned_to_nat(1);
                            v___x_9605_ = lean_mk_empty_array_with_capacity(v___x_9604_);
                            v___x_9606_ = lean_array_push(v___x_9605_, v_binderType_9599_);
                            v___x_9607_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_9606_, v_givenNames_9589_, v___f_9603_, v_config_9590_, v___y_9591_, v___y_9592_, v___y_9593_, v___y_9594_);
                            return v___x_9607_;
                        }
                        8 => {
                            v_declName_9608_ = leanh::lean_ctor_get(v_a_9597_, 0);
                            leanh::lean_inc(v_declName_9608_);
                            v_type_9609_ = leanh::lean_ctor_get(v_a_9597_, 1);
                            leanh::lean_inc_ref_n(v_type_9609_, 2);
                            v_value_9610_ = leanh::lean_ctor_get(v_a_9597_, 2);
                            leanh::lean_inc_ref_n(v_value_9610_, 2);
                            v_body_9611_ = leanh::lean_ctor_get(v_a_9597_, 3);
                            leanh::lean_inc_ref(v_body_9611_);
                            v_nondep_9612_ = leanh::lean_ctor_get_uint8(
                                v_a_9597_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8)
                                    as u32,
                            );
                            leanh::lean_dec_ref_known(v_a_9597_, 4);
                            v___x_9613_ = leanh::lean_box((v_nondep_9612_) as usize);
                            v___f_9614_ = leanh::lean_alloc_closure(
                                l_Lean_MVarId_extractLetsLocalDecl___lam__2___boxed
                                    as *mut core::ffi::c_void,
                                17,
                                9,
                            );
                            leanh::lean_closure_set(v___f_9614_, 0, v___x_9586_);
                            leanh::lean_closure_set(v___f_9614_, 1, v_declName_9608_);
                            leanh::lean_closure_set(v___f_9614_, 2, v_body_9611_);
                            leanh::lean_closure_set(v___f_9614_, 3, v___x_9613_);
                            leanh::lean_closure_set(v___f_9614_, 4, v___f_9587_);
                            leanh::lean_closure_set(v___f_9614_, 5, v_value_9610_);
                            leanh::lean_closure_set(v___f_9614_, 6, v___x_9588_);
                            leanh::lean_closure_set(v___f_9614_, 7, v_mvarId_9585_);
                            leanh::lean_closure_set(v___f_9614_, 8, v_type_9609_);
                            v___x_9615_ = leanh::lean_unsigned_to_nat(2);
                            v___x_9616_ = lean_mk_empty_array_with_capacity(v___x_9615_);
                            v___x_9617_ = lean_array_push(v___x_9616_, v_type_9609_);
                            v___x_9618_ = lean_array_push(v___x_9617_, v_value_9610_);
                            v___x_9619_ = l_Lean_Meta_extractLets___at___00Lean_MVarId_extractLets_spec__2___redArg(v___x_9618_, v_givenNames_9589_, v___f_9614_, v_config_9590_, v___y_9591_, v___y_9592_, v___y_9593_, v___y_9594_);
                            return v___x_9619_;
                        }
                        _ => {
                            leanh::lean_dec(v_a_9597_);
                            leanh::lean_dec(v_givenNames_9589_);
                            leanh::lean_dec_ref(v___f_9587_);
                            leanh::lean_dec_ref(v___x_9586_);
                            v___x_9620_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once
                                ),
                                _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3,
                            );
                            v___x_9621_ = l_Lean_Meta_throwTacticEx___redArg(
                                v___x_9588_,
                                v_mvarId_9585_,
                                v___x_9620_,
                                v___y_9591_,
                                v___y_9592_,
                                v___y_9593_,
                                v___y_9594_,
                            );
                            return v___x_9621_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_givenNames_9589_);
                    leanh::lean_dec(v___x_9588_);
                    leanh::lean_dec_ref(v___f_9587_);
                    leanh::lean_dec_ref(v___x_9586_);
                    leanh::lean_dec(v_mvarId_9585_);
                    v_a_9622_ = leanh::lean_ctor_get(v___x_9596_, 0);
                    v_isSharedCheck_9629_ = (!leanh::lean_is_exclusive(v___x_9596_)) as u8;
                    if v_isSharedCheck_9629_ == 0 {
                        v___x_9624_ = v___x_9596_;
                        v_isShared_9625_ = v_isSharedCheck_9629_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9622_);
                        leanh::lean_dec(v___x_9596_);
                        v___x_9624_ = leanh::lean_box(0);
                        v_isShared_9625_ = v_isSharedCheck_9629_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9625_ == 0 {
                    v___x_9627_ = v___x_9624_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9628_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9628_, 0, v_a_9622_);
                    v___x_9627_ = v_reuseFailAlloc_9628_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9627_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed(
    mut v_mvarId_9630_: *mut leanh::LeanObject,
    mut v___x_9631_: *mut leanh::LeanObject,
    mut v___f_9632_: *mut leanh::LeanObject,
    mut v___x_9633_: *mut leanh::LeanObject,
    mut v_givenNames_9634_: *mut leanh::LeanObject,
    mut v_config_9635_: *mut leanh::LeanObject,
    mut v___y_9636_: *mut leanh::LeanObject,
    mut v___y_9637_: *mut leanh::LeanObject,
    mut v___y_9638_: *mut leanh::LeanObject,
    mut v___y_9639_: *mut leanh::LeanObject,
    mut v___y_9640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9641_ = l_Lean_MVarId_extractLetsLocalDecl___lam__3(
        v_mvarId_9630_,
        v___x_9631_,
        v___f_9632_,
        v___x_9633_,
        v_givenNames_9634_,
        v_config_9635_,
        v___y_9636_,
        v___y_9637_,
        v___y_9638_,
        v___y_9639_,
    );
    leanh::lean_dec(v___y_9639_);
    leanh::lean_dec_ref(v___y_9638_);
    leanh::lean_dec(v___y_9637_);
    leanh::lean_dec_ref(v___y_9636_);
    leanh::lean_dec_ref(v_config_9635_);
    return v_res_9641_;
}
pub unsafe fn l_Lean_MVarId_extractLetsLocalDecl___lam__4(
    mut v___x_9642_: *mut leanh::LeanObject,
    mut v___x_9643_: *mut leanh::LeanObject,
    mut v_givenNames_9644_: *mut leanh::LeanObject,
    mut v_config_9645_: *mut leanh::LeanObject,
    mut v_mvarId_9646_: *mut leanh::LeanObject,
    mut v_fvars_9647_: *mut leanh::LeanObject,
    mut v___y_9648_: *mut leanh::LeanObject,
    mut v___y_9649_: *mut leanh::LeanObject,
    mut v___y_9650_: *mut leanh::LeanObject,
    mut v___y_9651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_9653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9655_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v_mvarId_9646_, 2);
    v___f_9653_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_extractLetsLocalDecl___lam__0___boxed as *mut core::ffi::c_void,
        10,
        2,
    );
    leanh::lean_closure_set(v___f_9653_, 0, v_mvarId_9646_);
    leanh::lean_closure_set(v___f_9653_, 1, v_fvars_9647_);
    v___f_9654_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_extractLetsLocalDecl___lam__3___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    leanh::lean_closure_set(v___f_9654_, 0, v_mvarId_9646_);
    leanh::lean_closure_set(v___f_9654_, 1, v___x_9642_);
    leanh::lean_closure_set(v___f_9654_, 2, v___f_9653_);
    leanh::lean_closure_set(v___f_9654_, 3, v___x_9643_);
    leanh::lean_closure_set(v___f_9654_, 4, v_givenNames_9644_);
    leanh::lean_closure_set(v___f_9654_, 5, v_config_9645_);
    v___x_9655_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(
        v_mvarId_9646_,
        v___f_9654_,
        v___y_9648_,
        v___y_9649_,
        v___y_9650_,
        v___y_9651_,
    );
    return v___x_9655_;
}
pub unsafe fn l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed(
    mut v___x_9656_: *mut leanh::LeanObject,
    mut v___x_9657_: *mut leanh::LeanObject,
    mut v_givenNames_9658_: *mut leanh::LeanObject,
    mut v_config_9659_: *mut leanh::LeanObject,
    mut v_mvarId_9660_: *mut leanh::LeanObject,
    mut v_fvars_9661_: *mut leanh::LeanObject,
    mut v___y_9662_: *mut leanh::LeanObject,
    mut v___y_9663_: *mut leanh::LeanObject,
    mut v___y_9664_: *mut leanh::LeanObject,
    mut v___y_9665_: *mut leanh::LeanObject,
    mut v___y_9666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9667_ = l_Lean_MVarId_extractLetsLocalDecl___lam__4(
        v___x_9656_,
        v___x_9657_,
        v_givenNames_9658_,
        v_config_9659_,
        v_mvarId_9660_,
        v_fvars_9661_,
        v___y_9662_,
        v___y_9663_,
        v___y_9664_,
        v___y_9665_,
    );
    leanh::lean_dec(v___y_9665_);
    leanh::lean_dec_ref(v___y_9664_);
    leanh::lean_dec(v___y_9663_);
    leanh::lean_dec_ref(v___y_9662_);
    return v_res_9667_;
}
pub unsafe fn l_Lean_MVarId_extractLetsLocalDecl(
    mut v_mvarId_9668_: *mut leanh::LeanObject,
    mut v_fvarId_9669_: *mut leanh::LeanObject,
    mut v_givenNames_9670_: *mut leanh::LeanObject,
    mut v_config_9671_: *mut leanh::LeanObject,
    mut v_a_9672_: *mut leanh::LeanObject,
    mut v_a_9673_: *mut leanh::LeanObject,
    mut v_a_9674_: *mut leanh::LeanObject,
    mut v_a_9675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9684_: u8 = 0;
    let mut v___x_9685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9689_: u8 = 0;
    let mut v___x_9691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9693_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9677_ = l_Lean_MVarId_extractLets___closed__1;
                leanh::lean_inc(v_mvarId_9668_);
                v___x_9678_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_9668_,
                    v___x_9677_,
                    v_a_9672_,
                    v_a_9673_,
                    v_a_9674_,
                    v_a_9675_,
                );
                if leanh::lean_obj_tag(v___x_9678_) == 0 {
                    leanh::lean_dec_ref_known(v___x_9678_, 1);
                    v___x_9679_ = l_Lean_instInhabitedExpr;
                    v___f_9680_ = leanh::lean_alloc_closure(
                        l_Lean_MVarId_extractLetsLocalDecl___lam__4___boxed
                            as *mut core::ffi::c_void,
                        11,
                        4,
                    );
                    leanh::lean_closure_set(v___f_9680_, 0, v___x_9679_);
                    leanh::lean_closure_set(v___f_9680_, 1, v___x_9677_);
                    leanh::lean_closure_set(v___f_9680_, 2, v_givenNames_9670_);
                    leanh::lean_closure_set(v___f_9680_, 3, v_config_9671_);
                    v___x_9681_ = leanh::lean_unsigned_to_nat(1);
                    v___x_9682_ = lean_mk_empty_array_with_capacity(v___x_9681_);
                    v___x_9683_ = lean_array_push(v___x_9682_, v_fvarId_9669_);
                    v___x_9684_ = 0;
                    v___x_9685_ = l_Lean_MVarId_withReverted___redArg(
                        v_mvarId_9668_,
                        v___x_9683_,
                        v___f_9680_,
                        v___x_9684_,
                        v_a_9672_,
                        v_a_9673_,
                        v_a_9674_,
                        v_a_9675_,
                    );
                    return v___x_9685_;
                } else {
                    leanh::lean_dec_ref(v_config_9671_);
                    leanh::lean_dec(v_givenNames_9670_);
                    leanh::lean_dec(v_fvarId_9669_);
                    leanh::lean_dec(v_mvarId_9668_);
                    v_a_9686_ = leanh::lean_ctor_get(v___x_9678_, 0);
                    v_isSharedCheck_9693_ = (!leanh::lean_is_exclusive(v___x_9678_)) as u8;
                    if v_isSharedCheck_9693_ == 0 {
                        v___x_9688_ = v___x_9678_;
                        v_isShared_9689_ = v_isSharedCheck_9693_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9686_);
                        leanh::lean_dec(v___x_9678_);
                        v___x_9688_ = leanh::lean_box(0);
                        v_isShared_9689_ = v_isSharedCheck_9693_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9689_ == 0 {
                    v___x_9691_ = v___x_9688_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9692_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9692_, 0, v_a_9686_);
                    v___x_9691_ = v_reuseFailAlloc_9692_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9691_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_extractLetsLocalDecl___boxed(
    mut v_mvarId_9694_: *mut leanh::LeanObject,
    mut v_fvarId_9695_: *mut leanh::LeanObject,
    mut v_givenNames_9696_: *mut leanh::LeanObject,
    mut v_config_9697_: *mut leanh::LeanObject,
    mut v_a_9698_: *mut leanh::LeanObject,
    mut v_a_9699_: *mut leanh::LeanObject,
    mut v_a_9700_: *mut leanh::LeanObject,
    mut v_a_9701_: *mut leanh::LeanObject,
    mut v_a_9702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9703_ = l_Lean_MVarId_extractLetsLocalDecl(
        v_mvarId_9694_,
        v_fvarId_9695_,
        v_givenNames_9696_,
        v_config_9697_,
        v_a_9698_,
        v_a_9699_,
        v_a_9700_,
        v_a_9701_,
    );
    leanh::lean_dec(v_a_9701_);
    leanh::lean_dec_ref(v_a_9700_);
    leanh::lean_dec(v_a_9699_);
    leanh::lean_dec_ref(v_a_9698_);
    return v_res_9703_;
}
pub unsafe fn l_Lean_MVarId_liftLets___lam__0(
    mut v_mvarId_9704_: *mut leanh::LeanObject,
    mut v___x_9705_: *mut leanh::LeanObject,
    mut v_config_9706_: *mut leanh::LeanObject,
    mut v___y_9707_: *mut leanh::LeanObject,
    mut v___y_9708_: *mut leanh::LeanObject,
    mut v___y_9709_: *mut leanh::LeanObject,
    mut v___y_9710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9717_: u8 = 0;
    let mut v___x_9718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9724_: u8 = 0;
    let mut v___x_9726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9728_: u8 = 0;
    let mut v_a_9729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9732_: u8 = 0;
    let mut v___x_9734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9736_: u8 = 0;
    let mut v_a_9737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9740_: u8 = 0;
    let mut v___x_9742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9744_: u8 = 0;
    let mut v_a_9745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9748_: u8 = 0;
    let mut v___x_9750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___x_9705_);
                leanh::lean_inc(v_mvarId_9704_);
                v___x_9712_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_9704_,
                    v___x_9705_,
                    v___y_9707_,
                    v___y_9708_,
                    v___y_9709_,
                    v___y_9710_,
                );
                if leanh::lean_obj_tag(v___x_9712_) == 0 {
                    leanh::lean_dec_ref_known(v___x_9712_, 1);
                    leanh::lean_inc(v_mvarId_9704_);
                    v___x_9713_ = l_Lean_MVarId_getType(
                        v_mvarId_9704_,
                        v___y_9707_,
                        v___y_9708_,
                        v___y_9709_,
                        v___y_9710_,
                    );
                    if leanh::lean_obj_tag(v___x_9713_) == 0 {
                        v_a_9714_ = leanh::lean_ctor_get(v___x_9713_, 0);
                        leanh::lean_inc_n(v_a_9714_, 2);
                        leanh::lean_dec_ref_known(v___x_9713_, 1);
                        v___x_9715_ = l_Lean_Meta_liftLets(
                            v_a_9714_,
                            v_config_9706_,
                            v___y_9707_,
                            v___y_9708_,
                            v___y_9709_,
                            v___y_9710_,
                        );
                        if leanh::lean_obj_tag(v___x_9715_) == 0 {
                            v_a_9716_ = leanh::lean_ctor_get(v___x_9715_, 0);
                            leanh::lean_inc(v_a_9716_);
                            leanh::lean_dec_ref_known(v___x_9715_, 1);
                            v___x_9717_ = lean_expr_eqv(v_a_9714_, v_a_9716_);
                            leanh::lean_dec(v_a_9714_);
                            if v___x_9717_ == 0 {
                                leanh::lean_dec(v___x_9705_);
                                v___x_9718_ = l_Lean_MVarId_replaceTargetDefEq(
                                    v_mvarId_9704_,
                                    v_a_9716_,
                                    v___y_9707_,
                                    v___y_9708_,
                                    v___y_9709_,
                                    v___y_9710_,
                                );
                                return v___x_9718_;
                            } else {
                                leanh::lean_inc(v_mvarId_9704_);
                                v___x_9719_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_9705_, v_mvarId_9704_, v___y_9707_, v___y_9708_, v___y_9709_, v___y_9710_);
                                if leanh::lean_obj_tag(v___x_9719_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_9719_, 1);
                                    v___x_9720_ = l_Lean_MVarId_replaceTargetDefEq(
                                        v_mvarId_9704_,
                                        v_a_9716_,
                                        v___y_9707_,
                                        v___y_9708_,
                                        v___y_9709_,
                                        v___y_9710_,
                                    );
                                    return v___x_9720_;
                                } else {
                                    leanh::lean_dec(v_a_9716_);
                                    leanh::lean_dec(v_mvarId_9704_);
                                    v_a_9721_ = leanh::lean_ctor_get(v___x_9719_, 0);
                                    v_isSharedCheck_9728_ =
                                        (!leanh::lean_is_exclusive(v___x_9719_)) as u8;
                                    if v_isSharedCheck_9728_ == 0 {
                                        v___x_9723_ = v___x_9719_;
                                        v_isShared_9724_ = v_isSharedCheck_9728_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_9721_);
                                        leanh::lean_dec(v___x_9719_);
                                        v___x_9723_ = leanh::lean_box(0);
                                        v_isShared_9724_ = v_isSharedCheck_9728_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_9714_);
                            leanh::lean_dec(v___x_9705_);
                            leanh::lean_dec(v_mvarId_9704_);
                            v_a_9729_ = leanh::lean_ctor_get(v___x_9715_, 0);
                            v_isSharedCheck_9736_ =
                                (!leanh::lean_is_exclusive(v___x_9715_)) as u8;
                            if v_isSharedCheck_9736_ == 0 {
                                v___x_9731_ = v___x_9715_;
                                v_isShared_9732_ = v_isSharedCheck_9736_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_9729_);
                                leanh::lean_dec(v___x_9715_);
                                v___x_9731_ = leanh::lean_box(0);
                                v_isShared_9732_ = v_isSharedCheck_9736_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_config_9706_);
                        leanh::lean_dec(v___x_9705_);
                        leanh::lean_dec(v_mvarId_9704_);
                        v_a_9737_ = leanh::lean_ctor_get(v___x_9713_, 0);
                        v_isSharedCheck_9744_ =
                            (!leanh::lean_is_exclusive(v___x_9713_)) as u8;
                        if v_isSharedCheck_9744_ == 0 {
                            v___x_9739_ = v___x_9713_;
                            v_isShared_9740_ = v_isSharedCheck_9744_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9737_);
                            leanh::lean_dec(v___x_9713_);
                            v___x_9739_ = leanh::lean_box(0);
                            v_isShared_9740_ = v_isSharedCheck_9744_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_config_9706_);
                    leanh::lean_dec(v___x_9705_);
                    leanh::lean_dec(v_mvarId_9704_);
                    v_a_9745_ = leanh::lean_ctor_get(v___x_9712_, 0);
                    v_isSharedCheck_9752_ = (!leanh::lean_is_exclusive(v___x_9712_)) as u8;
                    if v_isSharedCheck_9752_ == 0 {
                        v___x_9747_ = v___x_9712_;
                        v_isShared_9748_ = v_isSharedCheck_9752_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9745_);
                        leanh::lean_dec(v___x_9712_);
                        v___x_9747_ = leanh::lean_box(0);
                        v_isShared_9748_ = v_isSharedCheck_9752_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9724_ == 0 {
                    v___x_9726_ = v___x_9723_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9727_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9727_, 0, v_a_9721_);
                    v___x_9726_ = v_reuseFailAlloc_9727_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9726_;
            }
            3 => {
                if v_isShared_9732_ == 0 {
                    v___x_9734_ = v___x_9731_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9735_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9735_, 0, v_a_9729_);
                    v___x_9734_ = v_reuseFailAlloc_9735_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9734_;
            }
            5 => {
                if v_isShared_9740_ == 0 {
                    v___x_9742_ = v___x_9739_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_9743_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9743_, 0, v_a_9737_);
                    v___x_9742_ = v_reuseFailAlloc_9743_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_9742_;
            }
            7 => {
                if v_isShared_9748_ == 0 {
                    v___x_9750_ = v___x_9747_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_9751_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9751_, 0, v_a_9745_);
                    v___x_9750_ = v_reuseFailAlloc_9751_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_9750_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_liftLets___lam__0___boxed(
    mut v_mvarId_9753_: *mut leanh::LeanObject,
    mut v___x_9754_: *mut leanh::LeanObject,
    mut v_config_9755_: *mut leanh::LeanObject,
    mut v___y_9756_: *mut leanh::LeanObject,
    mut v___y_9757_: *mut leanh::LeanObject,
    mut v___y_9758_: *mut leanh::LeanObject,
    mut v___y_9759_: *mut leanh::LeanObject,
    mut v___y_9760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9761_ = l_Lean_MVarId_liftLets___lam__0(
        v_mvarId_9753_,
        v___x_9754_,
        v_config_9755_,
        v___y_9756_,
        v___y_9757_,
        v___y_9758_,
        v___y_9759_,
    );
    leanh::lean_dec(v___y_9759_);
    leanh::lean_dec_ref(v___y_9758_);
    leanh::lean_dec(v___y_9757_);
    leanh::lean_dec_ref(v___y_9756_);
    return v_res_9761_;
}
pub unsafe fn l_Lean_MVarId_liftLets(
    mut v_mvarId_9765_: *mut leanh::LeanObject,
    mut v_config_9766_: *mut leanh::LeanObject,
    mut v_a_9767_: *mut leanh::LeanObject,
    mut v_a_9768_: *mut leanh::LeanObject,
    mut v_a_9769_: *mut leanh::LeanObject,
    mut v_a_9770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9772_ = l_Lean_MVarId_liftLets___closed__1;
    leanh::lean_inc(v_mvarId_9765_);
    v___f_9773_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_liftLets___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___f_9773_, 0, v_mvarId_9765_);
    leanh::lean_closure_set(v___f_9773_, 1, v___x_9772_);
    leanh::lean_closure_set(v___f_9773_, 2, v_config_9766_);
    v___x_9774_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(
        v_mvarId_9765_,
        v___f_9773_,
        v_a_9767_,
        v_a_9768_,
        v_a_9769_,
        v_a_9770_,
    );
    return v___x_9774_;
}
pub unsafe fn l_Lean_MVarId_liftLets___boxed(
    mut v_mvarId_9775_: *mut leanh::LeanObject,
    mut v_config_9776_: *mut leanh::LeanObject,
    mut v_a_9777_: *mut leanh::LeanObject,
    mut v_a_9778_: *mut leanh::LeanObject,
    mut v_a_9779_: *mut leanh::LeanObject,
    mut v_a_9780_: *mut leanh::LeanObject,
    mut v_a_9781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9782_ = l_Lean_MVarId_liftLets(
        v_mvarId_9775_,
        v_config_9776_,
        v_a_9777_,
        v_a_9778_,
        v_a_9779_,
        v_a_9780_,
    );
    leanh::lean_dec(v_a_9780_);
    leanh::lean_dec_ref(v_a_9779_);
    leanh::lean_dec(v_a_9778_);
    leanh::lean_dec_ref(v_a_9777_);
    return v_res_9782_;
}
pub unsafe fn l_Lean_MVarId_liftLetsLocalDecl___lam__0(
    mut v_mvarId_9783_: *mut leanh::LeanObject,
    mut v_fvars_9784_: *mut leanh::LeanObject,
    mut v_targetNew_9785_: *mut leanh::LeanObject,
    mut v___y_9786_: *mut leanh::LeanObject,
    mut v___y_9787_: *mut leanh::LeanObject,
    mut v___y_9788_: *mut leanh::LeanObject,
    mut v___y_9789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9795_: u8 = 0;
    let mut v___x_9796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_9797_: usize = 0;
    let mut v___x_9798_: usize = 0;
    let mut v___x_9799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9805_: u8 = 0;
    let mut v_a_9806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9809_: u8 = 0;
    let mut v___x_9811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9813_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9791_ = l_Lean_MVarId_replaceTargetDefEq(
                    v_mvarId_9783_,
                    v_targetNew_9785_,
                    v___y_9786_,
                    v___y_9787_,
                    v___y_9788_,
                    v___y_9789_,
                );
                if leanh::lean_obj_tag(v___x_9791_) == 0 {
                    v_a_9792_ = leanh::lean_ctor_get(v___x_9791_, 0);
                    v_isSharedCheck_9805_ = (!leanh::lean_is_exclusive(v___x_9791_)) as u8;
                    if v_isSharedCheck_9805_ == 0 {
                        v___x_9794_ = v___x_9791_;
                        v_isShared_9795_ = v_isSharedCheck_9805_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9792_);
                        leanh::lean_dec(v___x_9791_);
                        v___x_9794_ = leanh::lean_box(0);
                        v_isShared_9795_ = v_isSharedCheck_9805_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_fvars_9784_);
                    v_a_9806_ = leanh::lean_ctor_get(v___x_9791_, 0);
                    v_isSharedCheck_9813_ = (!leanh::lean_is_exclusive(v___x_9791_)) as u8;
                    if v_isSharedCheck_9813_ == 0 {
                        v___x_9808_ = v___x_9791_;
                        v_isShared_9809_ = v_isSharedCheck_9813_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9806_);
                        leanh::lean_dec(v___x_9791_);
                        v___x_9808_ = leanh::lean_box(0);
                        v_isShared_9809_ = v_isSharedCheck_9813_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9796_ = leanh::lean_box(0);
                v_sz_9797_ = lean_array_size(v_fvars_9784_);
                v___x_9798_ = 0usize;
                v___x_9799_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_extractLetsLocalDecl_spec__0(v_sz_9797_, v___x_9798_, v_fvars_9784_);
                v___x_9800_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_9800_, 0, v___x_9799_);
                leanh::lean_ctor_set(v___x_9800_, 1, v_a_9792_);
                v___x_9801_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_9801_, 0, v___x_9796_);
                leanh::lean_ctor_set(v___x_9801_, 1, v___x_9800_);
                if v_isShared_9795_ == 0 {
                    leanh::lean_ctor_set(v___x_9794_, 0, v___x_9801_);
                    v___x_9803_ = v___x_9794_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9804_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9804_, 0, v___x_9801_);
                    v___x_9803_ = v_reuseFailAlloc_9804_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9803_;
            }
            3 => {
                if v_isShared_9809_ == 0 {
                    v___x_9811_ = v___x_9808_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9812_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9812_, 0, v_a_9806_);
                    v___x_9811_ = v_reuseFailAlloc_9812_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9811_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed(
    mut v_mvarId_9814_: *mut leanh::LeanObject,
    mut v_fvars_9815_: *mut leanh::LeanObject,
    mut v_targetNew_9816_: *mut leanh::LeanObject,
    mut v___y_9817_: *mut leanh::LeanObject,
    mut v___y_9818_: *mut leanh::LeanObject,
    mut v___y_9819_: *mut leanh::LeanObject,
    mut v___y_9820_: *mut leanh::LeanObject,
    mut v___y_9821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9822_ = l_Lean_MVarId_liftLetsLocalDecl___lam__0(
        v_mvarId_9814_,
        v_fvars_9815_,
        v_targetNew_9816_,
        v___y_9817_,
        v___y_9818_,
        v___y_9819_,
        v___y_9820_,
    );
    leanh::lean_dec(v___y_9820_);
    leanh::lean_dec_ref(v___y_9819_);
    leanh::lean_dec(v___y_9818_);
    leanh::lean_dec_ref(v___y_9817_);
    return v_res_9822_;
}
pub unsafe fn l_Lean_MVarId_liftLetsLocalDecl___lam__1(
    mut v_mvarId_9823_: *mut leanh::LeanObject,
    mut v_config_9824_: *mut leanh::LeanObject,
    mut v___f_9825_: *mut leanh::LeanObject,
    mut v___x_9826_: *mut leanh::LeanObject,
    mut v___y_9827_: *mut leanh::LeanObject,
    mut v___y_9828_: *mut leanh::LeanObject,
    mut v___y_9829_: *mut leanh::LeanObject,
    mut v___y_9830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_9834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_9835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_9836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_9837_: u8 = 0;
    let mut v___x_9838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9847_: u8 = 0;
    let mut v___x_9848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9852_: u8 = 0;
    let mut v___x_9854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9856_: u8 = 0;
    let mut v_a_9857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9860_: u8 = 0;
    let mut v___x_9862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9864_: u8 = 0;
    let mut v_declName_9865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_9866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_9867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_9868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_9869_: u8 = 0;
    let mut v___x_9870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9882_: u8 = 0;
    let mut v___x_9883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9887_: u8 = 0;
    let mut v___x_9889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9891_: u8 = 0;
    let mut v___x_9892_: u8 = 0;
    let mut v___x_9893_: u8 = 0;
    let mut v_a_9894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9897_: u8 = 0;
    let mut v___x_9899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9901_: u8 = 0;
    let mut v_a_9902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9905_: u8 = 0;
    let mut v___x_9907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9909_: u8 = 0;
    let mut v___x_9910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9915_: u8 = 0;
    let mut v___x_9917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_9823_);
                v___x_9832_ = l_Lean_MVarId_getType(
                    v_mvarId_9823_,
                    v___y_9827_,
                    v___y_9828_,
                    v___y_9829_,
                    v___y_9830_,
                );
                if leanh::lean_obj_tag(v___x_9832_) == 0 {
                    v_a_9833_ = leanh::lean_ctor_get(v___x_9832_, 0);
                    leanh::lean_inc(v_a_9833_);
                    leanh::lean_dec_ref_known(v___x_9832_, 1);
                    match leanh::lean_obj_tag(v_a_9833_) {
                        7 => {
                            v_binderName_9834_ = leanh::lean_ctor_get(v_a_9833_, 0);
                            leanh::lean_inc(v_binderName_9834_);
                            v_binderType_9835_ = leanh::lean_ctor_get(v_a_9833_, 1);
                            leanh::lean_inc_ref_n(v_binderType_9835_, 2);
                            v_body_9836_ = leanh::lean_ctor_get(v_a_9833_, 2);
                            leanh::lean_inc_ref(v_body_9836_);
                            v_binderInfo_9837_ = leanh::lean_ctor_get_uint8(
                                v_a_9833_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            leanh::lean_dec_ref_known(v_a_9833_, 3);
                            v___x_9838_ = l_Lean_Meta_liftLets(
                                v_binderType_9835_,
                                v_config_9824_,
                                v___y_9827_,
                                v___y_9828_,
                                v___y_9829_,
                                v___y_9830_,
                            );
                            if leanh::lean_obj_tag(v___x_9838_) == 0 {
                                v_a_9839_ = leanh::lean_ctor_get(v___x_9838_, 0);
                                leanh::lean_inc(v_a_9839_);
                                leanh::lean_dec_ref_known(v___x_9838_, 1);
                                v___x_9847_ = lean_expr_eqv(v_binderType_9835_, v_a_9839_);
                                leanh::lean_dec_ref(v_binderType_9835_);
                                if v___x_9847_ == 0 {
                                    leanh::lean_dec(v___x_9826_);
                                    leanh::lean_dec(v_mvarId_9823_);
                                    v___y_9841_ = v___y_9827_;
                                    v___y_9842_ = v___y_9828_;
                                    v___y_9843_ = v___y_9829_;
                                    v___y_9844_ = v___y_9830_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_9848_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_9826_, v_mvarId_9823_, v___y_9827_, v___y_9828_, v___y_9829_, v___y_9830_);
                                    if leanh::lean_obj_tag(v___x_9848_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_9848_, 1);
                                        v___y_9841_ = v___y_9827_;
                                        v___y_9842_ = v___y_9828_;
                                        v___y_9843_ = v___y_9829_;
                                        v___y_9844_ = v___y_9830_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_a_9839_);
                                        leanh::lean_dec_ref(v_body_9836_);
                                        leanh::lean_dec(v_binderName_9834_);
                                        leanh::lean_dec(v___y_9830_);
                                        leanh::lean_dec_ref(v___y_9829_);
                                        leanh::lean_dec(v___y_9828_);
                                        leanh::lean_dec_ref(v___y_9827_);
                                        leanh::lean_dec_ref(v___f_9825_);
                                        v_a_9849_ = leanh::lean_ctor_get(v___x_9848_, 0);
                                        v_isSharedCheck_9856_ =
                                            (!leanh::lean_is_exclusive(v___x_9848_)) as u8;
                                        if v_isSharedCheck_9856_ == 0 {
                                            v___x_9851_ = v___x_9848_;
                                            v_isShared_9852_ = v_isSharedCheck_9856_;
                                            state = 2;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_9849_);
                                            leanh::lean_dec(v___x_9848_);
                                            v___x_9851_ = leanh::lean_box(0);
                                            v_isShared_9852_ = v_isSharedCheck_9856_;
                                            state = 2;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_body_9836_);
                                leanh::lean_dec_ref(v_binderType_9835_);
                                leanh::lean_dec(v_binderName_9834_);
                                leanh::lean_dec(v___y_9830_);
                                leanh::lean_dec_ref(v___y_9829_);
                                leanh::lean_dec(v___y_9828_);
                                leanh::lean_dec_ref(v___y_9827_);
                                leanh::lean_dec(v___x_9826_);
                                leanh::lean_dec_ref(v___f_9825_);
                                leanh::lean_dec(v_mvarId_9823_);
                                v_a_9857_ = leanh::lean_ctor_get(v___x_9838_, 0);
                                v_isSharedCheck_9864_ =
                                    (!leanh::lean_is_exclusive(v___x_9838_)) as u8;
                                if v_isSharedCheck_9864_ == 0 {
                                    v___x_9859_ = v___x_9838_;
                                    v_isShared_9860_ = v_isSharedCheck_9864_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_9857_);
                                    leanh::lean_dec(v___x_9838_);
                                    v___x_9859_ = leanh::lean_box(0);
                                    v_isShared_9860_ = v_isSharedCheck_9864_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                        8 => {
                            v_declName_9865_ = leanh::lean_ctor_get(v_a_9833_, 0);
                            leanh::lean_inc(v_declName_9865_);
                            v_type_9866_ = leanh::lean_ctor_get(v_a_9833_, 1);
                            leanh::lean_inc_ref_n(v_type_9866_, 2);
                            v_value_9867_ = leanh::lean_ctor_get(v_a_9833_, 2);
                            leanh::lean_inc_ref(v_value_9867_);
                            v_body_9868_ = leanh::lean_ctor_get(v_a_9833_, 3);
                            leanh::lean_inc_ref(v_body_9868_);
                            v_nondep_9869_ = leanh::lean_ctor_get_uint8(
                                v_a_9833_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8)
                                    as u32,
                            );
                            leanh::lean_dec_ref_known(v_a_9833_, 4);
                            leanh::lean_inc_ref(v_config_9824_);
                            v___x_9870_ = l_Lean_Meta_liftLets(
                                v_type_9866_,
                                v_config_9824_,
                                v___y_9827_,
                                v___y_9828_,
                                v___y_9829_,
                                v___y_9830_,
                            );
                            if leanh::lean_obj_tag(v___x_9870_) == 0 {
                                v_a_9871_ = leanh::lean_ctor_get(v___x_9870_, 0);
                                leanh::lean_inc(v_a_9871_);
                                leanh::lean_dec_ref_known(v___x_9870_, 1);
                                leanh::lean_inc_ref(v_value_9867_);
                                v___x_9872_ = l_Lean_Meta_liftLets(
                                    v_value_9867_,
                                    v_config_9824_,
                                    v___y_9827_,
                                    v___y_9828_,
                                    v___y_9829_,
                                    v___y_9830_,
                                );
                                if leanh::lean_obj_tag(v___x_9872_) == 0 {
                                    v_a_9873_ = leanh::lean_ctor_get(v___x_9872_, 0);
                                    leanh::lean_inc(v_a_9873_);
                                    leanh::lean_dec_ref_known(v___x_9872_, 1);
                                    v___x_9892_ = lean_expr_eqv(v_type_9866_, v_a_9871_);
                                    leanh::lean_dec_ref(v_type_9866_);
                                    if v___x_9892_ == 0 {
                                        leanh::lean_dec_ref(v_value_9867_);
                                        v___y_9882_ = v___x_9892_;
                                        state = 7;
                                        continue;
                                    } else {
                                        v___x_9893_ = lean_expr_eqv(v_value_9867_, v_a_9873_);
                                        leanh::lean_dec_ref(v_value_9867_);
                                        v___y_9882_ = v___x_9893_;
                                        state = 7;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_9871_);
                                    leanh::lean_dec_ref(v_body_9868_);
                                    leanh::lean_dec_ref(v_value_9867_);
                                    leanh::lean_dec_ref(v_type_9866_);
                                    leanh::lean_dec(v_declName_9865_);
                                    leanh::lean_dec(v___y_9830_);
                                    leanh::lean_dec_ref(v___y_9829_);
                                    leanh::lean_dec(v___y_9828_);
                                    leanh::lean_dec_ref(v___y_9827_);
                                    leanh::lean_dec(v___x_9826_);
                                    leanh::lean_dec_ref(v___f_9825_);
                                    leanh::lean_dec(v_mvarId_9823_);
                                    v_a_9894_ = leanh::lean_ctor_get(v___x_9872_, 0);
                                    v_isSharedCheck_9901_ =
                                        (!leanh::lean_is_exclusive(v___x_9872_)) as u8;
                                    if v_isSharedCheck_9901_ == 0 {
                                        v___x_9896_ = v___x_9872_;
                                        v_isShared_9897_ = v_isSharedCheck_9901_;
                                        state = 10;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_9894_);
                                        leanh::lean_dec(v___x_9872_);
                                        v___x_9896_ = leanh::lean_box(0);
                                        v_isShared_9897_ = v_isSharedCheck_9901_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_body_9868_);
                                leanh::lean_dec_ref(v_value_9867_);
                                leanh::lean_dec_ref(v_type_9866_);
                                leanh::lean_dec(v_declName_9865_);
                                leanh::lean_dec(v___y_9830_);
                                leanh::lean_dec_ref(v___y_9829_);
                                leanh::lean_dec(v___y_9828_);
                                leanh::lean_dec_ref(v___y_9827_);
                                leanh::lean_dec(v___x_9826_);
                                leanh::lean_dec_ref(v___f_9825_);
                                leanh::lean_dec_ref(v_config_9824_);
                                leanh::lean_dec(v_mvarId_9823_);
                                v_a_9902_ = leanh::lean_ctor_get(v___x_9870_, 0);
                                v_isSharedCheck_9909_ =
                                    (!leanh::lean_is_exclusive(v___x_9870_)) as u8;
                                if v_isSharedCheck_9909_ == 0 {
                                    v___x_9904_ = v___x_9870_;
                                    v_isShared_9905_ = v_isSharedCheck_9909_;
                                    state = 12;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_9902_);
                                    leanh::lean_dec(v___x_9870_);
                                    v___x_9904_ = leanh::lean_box(0);
                                    v_isShared_9905_ = v_isSharedCheck_9909_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            leanh::lean_dec(v_a_9833_);
                            leanh::lean_dec_ref(v___f_9825_);
                            leanh::lean_dec_ref(v_config_9824_);
                            v___x_9910_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3_once
                                ),
                                _init_l_Lean_MVarId_extractLetsLocalDecl___lam__3___closed__3,
                            );
                            v___x_9911_ = l_Lean_Meta_throwTacticEx___redArg(
                                v___x_9826_,
                                v_mvarId_9823_,
                                v___x_9910_,
                                v___y_9827_,
                                v___y_9828_,
                                v___y_9829_,
                                v___y_9830_,
                            );
                            leanh::lean_dec(v___y_9830_);
                            leanh::lean_dec_ref(v___y_9829_);
                            leanh::lean_dec(v___y_9828_);
                            leanh::lean_dec_ref(v___y_9827_);
                            return v___x_9911_;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_9830_);
                    leanh::lean_dec_ref(v___y_9829_);
                    leanh::lean_dec(v___y_9828_);
                    leanh::lean_dec_ref(v___y_9827_);
                    leanh::lean_dec(v___x_9826_);
                    leanh::lean_dec_ref(v___f_9825_);
                    leanh::lean_dec_ref(v_config_9824_);
                    leanh::lean_dec(v_mvarId_9823_);
                    v_a_9912_ = leanh::lean_ctor_get(v___x_9832_, 0);
                    v_isSharedCheck_9919_ = (!leanh::lean_is_exclusive(v___x_9832_)) as u8;
                    if v_isSharedCheck_9919_ == 0 {
                        v___x_9914_ = v___x_9832_;
                        v_isShared_9915_ = v_isSharedCheck_9919_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9912_);
                        leanh::lean_dec(v___x_9832_);
                        v___x_9914_ = leanh::lean_box(0);
                        v_isShared_9915_ = v_isSharedCheck_9919_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9845_ = l_Lean_Expr_forallE___override(
                    v_binderName_9834_,
                    v_a_9839_,
                    v_body_9836_,
                    v_binderInfo_9837_,
                );
                v___x_9846_ = leanh::lean_apply_6(
                    v___f_9825_,
                    v___x_9845_,
                    v___y_9841_,
                    v___y_9842_,
                    v___y_9843_,
                    v___y_9844_,
                    leanh::lean_box(0),
                );
                return v___x_9846_;
            }
            2 => {
                if v_isShared_9852_ == 0 {
                    v___x_9854_ = v___x_9851_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9855_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9855_, 0, v_a_9849_);
                    v___x_9854_ = v_reuseFailAlloc_9855_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_9854_;
            }
            4 => {
                if v_isShared_9860_ == 0 {
                    v___x_9862_ = v___x_9859_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9863_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9863_, 0, v_a_9857_);
                    v___x_9862_ = v_reuseFailAlloc_9863_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_9862_;
            }
            6 => {
                v___x_9879_ = l_Lean_Expr_letE___override(
                    v_declName_9865_,
                    v_a_9871_,
                    v_a_9873_,
                    v_body_9868_,
                    v_nondep_9869_,
                );
                v___x_9880_ = leanh::lean_apply_6(
                    v___f_9825_,
                    v___x_9879_,
                    v___y_9875_,
                    v___y_9876_,
                    v___y_9877_,
                    v___y_9878_,
                    leanh::lean_box(0),
                );
                return v___x_9880_;
            }
            7 => {
                if v___y_9882_ == 0 {
                    leanh::lean_dec(v___x_9826_);
                    leanh::lean_dec(v_mvarId_9823_);
                    v___y_9875_ = v___y_9827_;
                    v___y_9876_ = v___y_9828_;
                    v___y_9877_ = v___y_9829_;
                    v___y_9878_ = v___y_9830_;
                    state = 6;
                    continue;
                } else {
                    v___x_9883_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(
                        v___x_9826_,
                        v_mvarId_9823_,
                        v___y_9827_,
                        v___y_9828_,
                        v___y_9829_,
                        v___y_9830_,
                    );
                    if leanh::lean_obj_tag(v___x_9883_) == 0 {
                        leanh::lean_dec_ref_known(v___x_9883_, 1);
                        v___y_9875_ = v___y_9827_;
                        v___y_9876_ = v___y_9828_;
                        v___y_9877_ = v___y_9829_;
                        v___y_9878_ = v___y_9830_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_9873_);
                        leanh::lean_dec(v_a_9871_);
                        leanh::lean_dec_ref(v_body_9868_);
                        leanh::lean_dec(v_declName_9865_);
                        leanh::lean_dec(v___y_9830_);
                        leanh::lean_dec_ref(v___y_9829_);
                        leanh::lean_dec(v___y_9828_);
                        leanh::lean_dec_ref(v___y_9827_);
                        leanh::lean_dec_ref(v___f_9825_);
                        v_a_9884_ = leanh::lean_ctor_get(v___x_9883_, 0);
                        v_isSharedCheck_9891_ =
                            (!leanh::lean_is_exclusive(v___x_9883_)) as u8;
                        if v_isSharedCheck_9891_ == 0 {
                            v___x_9886_ = v___x_9883_;
                            v_isShared_9887_ = v_isSharedCheck_9891_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9884_);
                            leanh::lean_dec(v___x_9883_);
                            v___x_9886_ = leanh::lean_box(0);
                            v_isShared_9887_ = v_isSharedCheck_9891_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            8 => {
                if v_isShared_9887_ == 0 {
                    v___x_9889_ = v___x_9886_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_9890_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9890_, 0, v_a_9884_);
                    v___x_9889_ = v_reuseFailAlloc_9890_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_9889_;
            }
            10 => {
                if v_isShared_9897_ == 0 {
                    v___x_9899_ = v___x_9896_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_9900_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9900_, 0, v_a_9894_);
                    v___x_9899_ = v_reuseFailAlloc_9900_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_9899_;
            }
            12 => {
                if v_isShared_9905_ == 0 {
                    v___x_9907_ = v___x_9904_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_9908_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9908_, 0, v_a_9902_);
                    v___x_9907_ = v_reuseFailAlloc_9908_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_9907_;
            }
            14 => {
                if v_isShared_9915_ == 0 {
                    v___x_9917_ = v___x_9914_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_9918_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9918_, 0, v_a_9912_);
                    v___x_9917_ = v_reuseFailAlloc_9918_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_9917_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed(
    mut v_mvarId_9920_: *mut leanh::LeanObject,
    mut v_config_9921_: *mut leanh::LeanObject,
    mut v___f_9922_: *mut leanh::LeanObject,
    mut v___x_9923_: *mut leanh::LeanObject,
    mut v___y_9924_: *mut leanh::LeanObject,
    mut v___y_9925_: *mut leanh::LeanObject,
    mut v___y_9926_: *mut leanh::LeanObject,
    mut v___y_9927_: *mut leanh::LeanObject,
    mut v___y_9928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9929_ = l_Lean_MVarId_liftLetsLocalDecl___lam__1(
        v_mvarId_9920_,
        v_config_9921_,
        v___f_9922_,
        v___x_9923_,
        v___y_9924_,
        v___y_9925_,
        v___y_9926_,
        v___y_9927_,
    );
    return v_res_9929_;
}
pub unsafe fn l_Lean_MVarId_liftLetsLocalDecl___lam__2(
    mut v_config_9930_: *mut leanh::LeanObject,
    mut v___x_9931_: *mut leanh::LeanObject,
    mut v_mvarId_9932_: *mut leanh::LeanObject,
    mut v_fvars_9933_: *mut leanh::LeanObject,
    mut v___y_9934_: *mut leanh::LeanObject,
    mut v___y_9935_: *mut leanh::LeanObject,
    mut v___y_9936_: *mut leanh::LeanObject,
    mut v___y_9937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_9939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9941_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v_mvarId_9932_, 2);
    v___f_9939_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_liftLetsLocalDecl___lam__0___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    leanh::lean_closure_set(v___f_9939_, 0, v_mvarId_9932_);
    leanh::lean_closure_set(v___f_9939_, 1, v_fvars_9933_);
    v___f_9940_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_liftLetsLocalDecl___lam__1___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___f_9940_, 0, v_mvarId_9932_);
    leanh::lean_closure_set(v___f_9940_, 1, v_config_9930_);
    leanh::lean_closure_set(v___f_9940_, 2, v___f_9939_);
    leanh::lean_closure_set(v___f_9940_, 3, v___x_9931_);
    v___x_9941_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(
        v_mvarId_9932_,
        v___f_9940_,
        v___y_9934_,
        v___y_9935_,
        v___y_9936_,
        v___y_9937_,
    );
    return v___x_9941_;
}
pub unsafe fn l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed(
    mut v_config_9942_: *mut leanh::LeanObject,
    mut v___x_9943_: *mut leanh::LeanObject,
    mut v_mvarId_9944_: *mut leanh::LeanObject,
    mut v_fvars_9945_: *mut leanh::LeanObject,
    mut v___y_9946_: *mut leanh::LeanObject,
    mut v___y_9947_: *mut leanh::LeanObject,
    mut v___y_9948_: *mut leanh::LeanObject,
    mut v___y_9949_: *mut leanh::LeanObject,
    mut v___y_9950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9951_ = l_Lean_MVarId_liftLetsLocalDecl___lam__2(
        v_config_9942_,
        v___x_9943_,
        v_mvarId_9944_,
        v_fvars_9945_,
        v___y_9946_,
        v___y_9947_,
        v___y_9948_,
        v___y_9949_,
    );
    leanh::lean_dec(v___y_9949_);
    leanh::lean_dec_ref(v___y_9948_);
    leanh::lean_dec(v___y_9947_);
    leanh::lean_dec_ref(v___y_9946_);
    return v_res_9951_;
}
pub unsafe fn l_Lean_MVarId_liftLetsLocalDecl(
    mut v_mvarId_9952_: *mut leanh::LeanObject,
    mut v_fvarId_9953_: *mut leanh::LeanObject,
    mut v_config_9954_: *mut leanh::LeanObject,
    mut v_a_9955_: *mut leanh::LeanObject,
    mut v_a_9956_: *mut leanh::LeanObject,
    mut v_a_9957_: *mut leanh::LeanObject,
    mut v_a_9958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9966_: u8 = 0;
    let mut v___x_9967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9971_: u8 = 0;
    let mut v_snd_9972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9976_: u8 = 0;
    let mut v_a_9977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9980_: u8 = 0;
    let mut v___x_9982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9984_: u8 = 0;
    let mut v_a_9985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9988_: u8 = 0;
    let mut v___x_9990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9992_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9960_ = l_Lean_MVarId_liftLets___closed__1;
                leanh::lean_inc(v_mvarId_9952_);
                v___x_9961_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_9952_,
                    v___x_9960_,
                    v_a_9955_,
                    v_a_9956_,
                    v_a_9957_,
                    v_a_9958_,
                );
                if leanh::lean_obj_tag(v___x_9961_) == 0 {
                    leanh::lean_dec_ref_known(v___x_9961_, 1);
                    v___f_9962_ = leanh::lean_alloc_closure(
                        l_Lean_MVarId_liftLetsLocalDecl___lam__2___boxed as *mut core::ffi::c_void,
                        9,
                        2,
                    );
                    leanh::lean_closure_set(v___f_9962_, 0, v_config_9954_);
                    leanh::lean_closure_set(v___f_9962_, 1, v___x_9960_);
                    v___x_9963_ = leanh::lean_unsigned_to_nat(1);
                    v___x_9964_ = lean_mk_empty_array_with_capacity(v___x_9963_);
                    v___x_9965_ = lean_array_push(v___x_9964_, v_fvarId_9953_);
                    v___x_9966_ = 0;
                    v___x_9967_ = l_Lean_MVarId_withReverted___redArg(
                        v_mvarId_9952_,
                        v___x_9965_,
                        v___f_9962_,
                        v___x_9966_,
                        v_a_9955_,
                        v_a_9956_,
                        v_a_9957_,
                        v_a_9958_,
                    );
                    if leanh::lean_obj_tag(v___x_9967_) == 0 {
                        v_a_9968_ = leanh::lean_ctor_get(v___x_9967_, 0);
                        v_isSharedCheck_9976_ =
                            (!leanh::lean_is_exclusive(v___x_9967_)) as u8;
                        if v_isSharedCheck_9976_ == 0 {
                            v___x_9970_ = v___x_9967_;
                            v_isShared_9971_ = v_isSharedCheck_9976_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9968_);
                            leanh::lean_dec(v___x_9967_);
                            v___x_9970_ = leanh::lean_box(0);
                            v_isShared_9971_ = v_isSharedCheck_9976_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_9977_ = leanh::lean_ctor_get(v___x_9967_, 0);
                        v_isSharedCheck_9984_ =
                            (!leanh::lean_is_exclusive(v___x_9967_)) as u8;
                        if v_isSharedCheck_9984_ == 0 {
                            v___x_9979_ = v___x_9967_;
                            v_isShared_9980_ = v_isSharedCheck_9984_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9977_);
                            leanh::lean_dec(v___x_9967_);
                            v___x_9979_ = leanh::lean_box(0);
                            v_isShared_9980_ = v_isSharedCheck_9984_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_config_9954_);
                    leanh::lean_dec(v_fvarId_9953_);
                    leanh::lean_dec(v_mvarId_9952_);
                    v_a_9985_ = leanh::lean_ctor_get(v___x_9961_, 0);
                    v_isSharedCheck_9992_ = (!leanh::lean_is_exclusive(v___x_9961_)) as u8;
                    if v_isSharedCheck_9992_ == 0 {
                        v___x_9987_ = v___x_9961_;
                        v_isShared_9988_ = v_isSharedCheck_9992_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9985_);
                        leanh::lean_dec(v___x_9961_);
                        v___x_9987_ = leanh::lean_box(0);
                        v_isShared_9988_ = v_isSharedCheck_9992_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_9972_ = leanh::lean_ctor_get(v_a_9968_, 1);
                leanh::lean_inc(v_snd_9972_);
                leanh::lean_dec(v_a_9968_);
                if v_isShared_9971_ == 0 {
                    leanh::lean_ctor_set(v___x_9970_, 0, v_snd_9972_);
                    v___x_9974_ = v___x_9970_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9975_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9975_, 0, v_snd_9972_);
                    v___x_9974_ = v_reuseFailAlloc_9975_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9974_;
            }
            3 => {
                if v_isShared_9980_ == 0 {
                    v___x_9982_ = v___x_9979_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9983_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9983_, 0, v_a_9977_);
                    v___x_9982_ = v_reuseFailAlloc_9983_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9982_;
            }
            5 => {
                if v_isShared_9988_ == 0 {
                    v___x_9990_ = v___x_9987_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_9991_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9991_, 0, v_a_9985_);
                    v___x_9990_ = v_reuseFailAlloc_9991_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_9990_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_liftLetsLocalDecl___boxed(
    mut v_mvarId_9993_: *mut leanh::LeanObject,
    mut v_fvarId_9994_: *mut leanh::LeanObject,
    mut v_config_9995_: *mut leanh::LeanObject,
    mut v_a_9996_: *mut leanh::LeanObject,
    mut v_a_9997_: *mut leanh::LeanObject,
    mut v_a_9998_: *mut leanh::LeanObject,
    mut v_a_9999_: *mut leanh::LeanObject,
    mut v_a_10000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_10001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_10001_ = l_Lean_MVarId_liftLetsLocalDecl(
        v_mvarId_9993_,
        v_fvarId_9994_,
        v_config_9995_,
        v_a_9996_,
        v_a_9997_,
        v_a_9998_,
        v_a_9999_,
    );
    leanh::lean_dec(v_a_9999_);
    leanh::lean_dec_ref(v_a_9998_);
    leanh::lean_dec(v_a_9997_);
    leanh::lean_dec_ref(v_a_9996_);
    return v_res_10001_;
}
pub unsafe fn l_Lean_MVarId_letToHave___lam__0(
    mut v_mvarId_10002_: *mut leanh::LeanObject,
    mut v___x_10003_: *mut leanh::LeanObject,
    mut v_failIfUnchanged_10004_: u8,
    mut v___y_10005_: *mut leanh::LeanObject,
    mut v___y_10006_: *mut leanh::LeanObject,
    mut v___y_10007_: *mut leanh::LeanObject,
    mut v___y_10008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_10012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_10014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_10016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10017_: u8 = 0;
    let mut v___x_10018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_10021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10024_: u8 = 0;
    let mut v___x_10026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10028_: u8 = 0;
    let mut v_a_10029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10032_: u8 = 0;
    let mut v___x_10034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10036_: u8 = 0;
    let mut v_a_10037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10040_: u8 = 0;
    let mut v___x_10042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10044_: u8 = 0;
    let mut v_a_10045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10048_: u8 = 0;
    let mut v___x_10050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10052_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___x_10003_);
                leanh::lean_inc(v_mvarId_10002_);
                v___x_10010_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_10002_,
                    v___x_10003_,
                    v___y_10005_,
                    v___y_10006_,
                    v___y_10007_,
                    v___y_10008_,
                );
                if leanh::lean_obj_tag(v___x_10010_) == 0 {
                    leanh::lean_dec_ref_known(v___x_10010_, 1);
                    leanh::lean_inc(v_mvarId_10002_);
                    v___x_10011_ = l_Lean_MVarId_getType(
                        v_mvarId_10002_,
                        v___y_10005_,
                        v___y_10006_,
                        v___y_10007_,
                        v___y_10008_,
                    );
                    if leanh::lean_obj_tag(v___x_10011_) == 0 {
                        v_a_10012_ = leanh::lean_ctor_get(v___x_10011_, 0);
                        leanh::lean_inc_n(v_a_10012_, 2);
                        leanh::lean_dec_ref_known(v___x_10011_, 1);
                        v___x_10013_ = l_Lean_Meta_letToHave(
                            v_a_10012_,
                            v___y_10005_,
                            v___y_10006_,
                            v___y_10007_,
                            v___y_10008_,
                        );
                        if leanh::lean_obj_tag(v___x_10013_) == 0 {
                            if v_failIfUnchanged_10004_ == 0 {
                                leanh::lean_dec(v_a_10012_);
                                leanh::lean_dec(v___x_10003_);
                                v_a_10014_ = leanh::lean_ctor_get(v___x_10013_, 0);
                                leanh::lean_inc(v_a_10014_);
                                leanh::lean_dec_ref_known(v___x_10013_, 1);
                                v___x_10015_ = l_Lean_MVarId_replaceTargetDefEq(
                                    v_mvarId_10002_,
                                    v_a_10014_,
                                    v___y_10005_,
                                    v___y_10006_,
                                    v___y_10007_,
                                    v___y_10008_,
                                );
                                return v___x_10015_;
                            } else {
                                v_a_10016_ = leanh::lean_ctor_get(v___x_10013_, 0);
                                leanh::lean_inc(v_a_10016_);
                                leanh::lean_dec_ref_known(v___x_10013_, 1);
                                v___x_10017_ = lean_expr_eqv(v_a_10012_, v_a_10016_);
                                leanh::lean_dec(v_a_10012_);
                                if v___x_10017_ == 0 {
                                    leanh::lean_dec(v___x_10003_);
                                    v___x_10018_ = l_Lean_MVarId_replaceTargetDefEq(
                                        v_mvarId_10002_,
                                        v_a_10016_,
                                        v___y_10005_,
                                        v___y_10006_,
                                        v___y_10007_,
                                        v___y_10008_,
                                    );
                                    return v___x_10018_;
                                } else {
                                    leanh::lean_inc(v_mvarId_10002_);
                                    v___x_10019_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_10003_, v_mvarId_10002_, v___y_10005_, v___y_10006_, v___y_10007_, v___y_10008_);
                                    if leanh::lean_obj_tag(v___x_10019_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_10019_, 1);
                                        v___x_10020_ = l_Lean_MVarId_replaceTargetDefEq(
                                            v_mvarId_10002_,
                                            v_a_10016_,
                                            v___y_10005_,
                                            v___y_10006_,
                                            v___y_10007_,
                                            v___y_10008_,
                                        );
                                        return v___x_10020_;
                                    } else {
                                        leanh::lean_dec(v_a_10016_);
                                        leanh::lean_dec(v_mvarId_10002_);
                                        v_a_10021_ = leanh::lean_ctor_get(v___x_10019_, 0);
                                        v_isSharedCheck_10028_ =
                                            (!leanh::lean_is_exclusive(v___x_10019_)) as u8;
                                        if v_isSharedCheck_10028_ == 0 {
                                            v___x_10023_ = v___x_10019_;
                                            v_isShared_10024_ = v_isSharedCheck_10028_;
                                            state = 1;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_10021_);
                                            leanh::lean_dec(v___x_10019_);
                                            v___x_10023_ = leanh::lean_box(0);
                                            v_isShared_10024_ = v_isSharedCheck_10028_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_10012_);
                            leanh::lean_dec(v___x_10003_);
                            leanh::lean_dec(v_mvarId_10002_);
                            v_a_10029_ = leanh::lean_ctor_get(v___x_10013_, 0);
                            v_isSharedCheck_10036_ =
                                (!leanh::lean_is_exclusive(v___x_10013_)) as u8;
                            if v_isSharedCheck_10036_ == 0 {
                                v___x_10031_ = v___x_10013_;
                                v_isShared_10032_ = v_isSharedCheck_10036_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_10029_);
                                leanh::lean_dec(v___x_10013_);
                                v___x_10031_ = leanh::lean_box(0);
                                v_isShared_10032_ = v_isSharedCheck_10036_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_10003_);
                        leanh::lean_dec(v_mvarId_10002_);
                        v_a_10037_ = leanh::lean_ctor_get(v___x_10011_, 0);
                        v_isSharedCheck_10044_ =
                            (!leanh::lean_is_exclusive(v___x_10011_)) as u8;
                        if v_isSharedCheck_10044_ == 0 {
                            v___x_10039_ = v___x_10011_;
                            v_isShared_10040_ = v_isSharedCheck_10044_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_10037_);
                            leanh::lean_dec(v___x_10011_);
                            v___x_10039_ = leanh::lean_box(0);
                            v_isShared_10040_ = v_isSharedCheck_10044_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_10003_);
                    leanh::lean_dec(v_mvarId_10002_);
                    v_a_10045_ = leanh::lean_ctor_get(v___x_10010_, 0);
                    v_isSharedCheck_10052_ = (!leanh::lean_is_exclusive(v___x_10010_)) as u8;
                    if v_isSharedCheck_10052_ == 0 {
                        v___x_10047_ = v___x_10010_;
                        v_isShared_10048_ = v_isSharedCheck_10052_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_10045_);
                        leanh::lean_dec(v___x_10010_);
                        v___x_10047_ = leanh::lean_box(0);
                        v_isShared_10048_ = v_isSharedCheck_10052_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_10024_ == 0 {
                    v___x_10026_ = v___x_10023_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10027_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10027_, 0, v_a_10021_);
                    v___x_10026_ = v_reuseFailAlloc_10027_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_10026_;
            }
            3 => {
                if v_isShared_10032_ == 0 {
                    v___x_10034_ = v___x_10031_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10035_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10035_, 0, v_a_10029_);
                    v___x_10034_ = v_reuseFailAlloc_10035_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_10034_;
            }
            5 => {
                if v_isShared_10040_ == 0 {
                    v___x_10042_ = v___x_10039_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_10043_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10043_, 0, v_a_10037_);
                    v___x_10042_ = v_reuseFailAlloc_10043_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_10042_;
            }
            7 => {
                if v_isShared_10048_ == 0 {
                    v___x_10050_ = v___x_10047_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_10051_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10051_, 0, v_a_10045_);
                    v___x_10050_ = v_reuseFailAlloc_10051_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_10050_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_letToHave___lam__0___boxed(
    mut v_mvarId_10053_: *mut leanh::LeanObject,
    mut v___x_10054_: *mut leanh::LeanObject,
    mut v_failIfUnchanged_10055_: *mut leanh::LeanObject,
    mut v___y_10056_: *mut leanh::LeanObject,
    mut v___y_10057_: *mut leanh::LeanObject,
    mut v___y_10058_: *mut leanh::LeanObject,
    mut v___y_10059_: *mut leanh::LeanObject,
    mut v___y_10060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_failIfUnchanged_boxed_10061_: u8 = 0;
    let mut v_res_10062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_failIfUnchanged_boxed_10061_ = (leanh::lean_unbox(v_failIfUnchanged_10055_) as u8);
    v_res_10062_ = l_Lean_MVarId_letToHave___lam__0(
        v_mvarId_10053_,
        v___x_10054_,
        v_failIfUnchanged_boxed_10061_,
        v___y_10056_,
        v___y_10057_,
        v___y_10058_,
        v___y_10059_,
    );
    leanh::lean_dec(v___y_10059_);
    leanh::lean_dec_ref(v___y_10058_);
    leanh::lean_dec(v___y_10057_);
    leanh::lean_dec_ref(v___y_10056_);
    return v_res_10062_;
}
pub unsafe fn l_Lean_MVarId_letToHave(
    mut v_mvarId_10066_: *mut leanh::LeanObject,
    mut v_failIfUnchanged_10067_: u8,
    mut v_a_10068_: *mut leanh::LeanObject,
    mut v_a_10069_: *mut leanh::LeanObject,
    mut v_a_10070_: *mut leanh::LeanObject,
    mut v_a_10071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_10075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10073_ = l_Lean_MVarId_letToHave___closed__1;
    v___x_10074_ = leanh::lean_box((v_failIfUnchanged_10067_) as usize);
    leanh::lean_inc(v_mvarId_10066_);
    v___f_10075_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_letToHave___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___f_10075_, 0, v_mvarId_10066_);
    leanh::lean_closure_set(v___f_10075_, 1, v___x_10073_);
    leanh::lean_closure_set(v___f_10075_, 2, v___x_10074_);
    v___x_10076_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(
        v_mvarId_10066_,
        v___f_10075_,
        v_a_10068_,
        v_a_10069_,
        v_a_10070_,
        v_a_10071_,
    );
    return v___x_10076_;
}
pub unsafe fn l_Lean_MVarId_letToHave___boxed(
    mut v_mvarId_10077_: *mut leanh::LeanObject,
    mut v_failIfUnchanged_10078_: *mut leanh::LeanObject,
    mut v_a_10079_: *mut leanh::LeanObject,
    mut v_a_10080_: *mut leanh::LeanObject,
    mut v_a_10081_: *mut leanh::LeanObject,
    mut v_a_10082_: *mut leanh::LeanObject,
    mut v_a_10083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_failIfUnchanged_boxed_10084_: u8 = 0;
    let mut v_res_10085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_failIfUnchanged_boxed_10084_ = (leanh::lean_unbox(v_failIfUnchanged_10078_) as u8);
    v_res_10085_ = l_Lean_MVarId_letToHave(
        v_mvarId_10077_,
        v_failIfUnchanged_boxed_10084_,
        v_a_10079_,
        v_a_10080_,
        v_a_10081_,
        v_a_10082_,
    );
    leanh::lean_dec(v_a_10082_);
    leanh::lean_dec_ref(v_a_10081_);
    leanh::lean_dec(v_a_10080_);
    leanh::lean_dec_ref(v_a_10079_);
    return v_res_10085_;
}
pub unsafe fn l_Lean_MVarId_letToHaveLocalDecl___lam__0(
    mut v_mvarId_10086_: *mut leanh::LeanObject,
    mut v___x_10087_: *mut leanh::LeanObject,
    mut v_fvarId_10088_: *mut leanh::LeanObject,
    mut v_failIfUnchanged_10089_: u8,
    mut v___y_10090_: *mut leanh::LeanObject,
    mut v___y_10091_: *mut leanh::LeanObject,
    mut v___y_10092_: *mut leanh::LeanObject,
    mut v___y_10093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_10097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_10099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_10101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10102_: u8 = 0;
    let mut v___x_10103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_10106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10109_: u8 = 0;
    let mut v___x_10111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10113_: u8 = 0;
    let mut v_a_10114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10117_: u8 = 0;
    let mut v___x_10119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10121_: u8 = 0;
    let mut v_a_10122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10125_: u8 = 0;
    let mut v___x_10127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10129_: u8 = 0;
    let mut v_a_10130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_10133_: u8 = 0;
    let mut v___x_10135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10137_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___x_10087_);
                leanh::lean_inc(v_mvarId_10086_);
                v___x_10095_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_10086_,
                    v___x_10087_,
                    v___y_10090_,
                    v___y_10091_,
                    v___y_10092_,
                    v___y_10093_,
                );
                if leanh::lean_obj_tag(v___x_10095_) == 0 {
                    leanh::lean_dec_ref_known(v___x_10095_, 1);
                    leanh::lean_inc(v_fvarId_10088_);
                    v___x_10096_ = l_Lean_FVarId_getType___redArg(
                        v_fvarId_10088_,
                        v___y_10090_,
                        v___y_10092_,
                        v___y_10093_,
                    );
                    if leanh::lean_obj_tag(v___x_10096_) == 0 {
                        v_a_10097_ = leanh::lean_ctor_get(v___x_10096_, 0);
                        leanh::lean_inc_n(v_a_10097_, 2);
                        leanh::lean_dec_ref_known(v___x_10096_, 1);
                        v___x_10098_ = l_Lean_Meta_letToHave(
                            v_a_10097_,
                            v___y_10090_,
                            v___y_10091_,
                            v___y_10092_,
                            v___y_10093_,
                        );
                        if leanh::lean_obj_tag(v___x_10098_) == 0 {
                            if v_failIfUnchanged_10089_ == 0 {
                                leanh::lean_dec(v_a_10097_);
                                leanh::lean_dec(v___x_10087_);
                                v_a_10099_ = leanh::lean_ctor_get(v___x_10098_, 0);
                                leanh::lean_inc(v_a_10099_);
                                leanh::lean_dec_ref_known(v___x_10098_, 1);
                                v___x_10100_ = l_Lean_MVarId_replaceLocalDeclDefEq(
                                    v_mvarId_10086_,
                                    v_fvarId_10088_,
                                    v_a_10099_,
                                    v___y_10090_,
                                    v___y_10091_,
                                    v___y_10092_,
                                    v___y_10093_,
                                );
                                return v___x_10100_;
                            } else {
                                v_a_10101_ = leanh::lean_ctor_get(v___x_10098_, 0);
                                leanh::lean_inc(v_a_10101_);
                                leanh::lean_dec_ref_known(v___x_10098_, 1);
                                v___x_10102_ = lean_expr_eqv(v_a_10097_, v_a_10101_);
                                leanh::lean_dec(v_a_10097_);
                                if v___x_10102_ == 0 {
                                    leanh::lean_dec(v___x_10087_);
                                    v___x_10103_ = l_Lean_MVarId_replaceLocalDeclDefEq(
                                        v_mvarId_10086_,
                                        v_fvarId_10088_,
                                        v_a_10101_,
                                        v___y_10090_,
                                        v___y_10091_,
                                        v___y_10092_,
                                        v___y_10093_,
                                    );
                                    return v___x_10103_;
                                } else {
                                    leanh::lean_inc(v_mvarId_10086_);
                                    v___x_10104_ = l___private_Lean_Meta_Tactic_Lets_0__throwMadeNoProgress___redArg(v___x_10087_, v_mvarId_10086_, v___y_10090_, v___y_10091_, v___y_10092_, v___y_10093_);
                                    if leanh::lean_obj_tag(v___x_10104_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_10104_, 1);
                                        v___x_10105_ = l_Lean_MVarId_replaceLocalDeclDefEq(
                                            v_mvarId_10086_,
                                            v_fvarId_10088_,
                                            v_a_10101_,
                                            v___y_10090_,
                                            v___y_10091_,
                                            v___y_10092_,
                                            v___y_10093_,
                                        );
                                        return v___x_10105_;
                                    } else {
                                        leanh::lean_dec(v_a_10101_);
                                        leanh::lean_dec(v_fvarId_10088_);
                                        leanh::lean_dec(v_mvarId_10086_);
                                        v_a_10106_ = leanh::lean_ctor_get(v___x_10104_, 0);
                                        v_isSharedCheck_10113_ =
                                            (!leanh::lean_is_exclusive(v___x_10104_)) as u8;
                                        if v_isSharedCheck_10113_ == 0 {
                                            v___x_10108_ = v___x_10104_;
                                            v_isShared_10109_ = v_isSharedCheck_10113_;
                                            state = 1;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_10106_);
                                            leanh::lean_dec(v___x_10104_);
                                            v___x_10108_ = leanh::lean_box(0);
                                            v_isShared_10109_ = v_isSharedCheck_10113_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_10097_);
                            leanh::lean_dec(v_fvarId_10088_);
                            leanh::lean_dec(v___x_10087_);
                            leanh::lean_dec(v_mvarId_10086_);
                            v_a_10114_ = leanh::lean_ctor_get(v___x_10098_, 0);
                            v_isSharedCheck_10121_ =
                                (!leanh::lean_is_exclusive(v___x_10098_)) as u8;
                            if v_isSharedCheck_10121_ == 0 {
                                v___x_10116_ = v___x_10098_;
                                v_isShared_10117_ = v_isSharedCheck_10121_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_10114_);
                                leanh::lean_dec(v___x_10098_);
                                v___x_10116_ = leanh::lean_box(0);
                                v_isShared_10117_ = v_isSharedCheck_10121_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_fvarId_10088_);
                        leanh::lean_dec(v___x_10087_);
                        leanh::lean_dec(v_mvarId_10086_);
                        v_a_10122_ = leanh::lean_ctor_get(v___x_10096_, 0);
                        v_isSharedCheck_10129_ =
                            (!leanh::lean_is_exclusive(v___x_10096_)) as u8;
                        if v_isSharedCheck_10129_ == 0 {
                            v___x_10124_ = v___x_10096_;
                            v_isShared_10125_ = v_isSharedCheck_10129_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_10122_);
                            leanh::lean_dec(v___x_10096_);
                            v___x_10124_ = leanh::lean_box(0);
                            v_isShared_10125_ = v_isSharedCheck_10129_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fvarId_10088_);
                    leanh::lean_dec(v___x_10087_);
                    leanh::lean_dec(v_mvarId_10086_);
                    v_a_10130_ = leanh::lean_ctor_get(v___x_10095_, 0);
                    v_isSharedCheck_10137_ = (!leanh::lean_is_exclusive(v___x_10095_)) as u8;
                    if v_isSharedCheck_10137_ == 0 {
                        v___x_10132_ = v___x_10095_;
                        v_isShared_10133_ = v_isSharedCheck_10137_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_10130_);
                        leanh::lean_dec(v___x_10095_);
                        v___x_10132_ = leanh::lean_box(0);
                        v_isShared_10133_ = v_isSharedCheck_10137_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_10109_ == 0 {
                    v___x_10111_ = v___x_10108_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10112_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10112_, 0, v_a_10106_);
                    v___x_10111_ = v_reuseFailAlloc_10112_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_10111_;
            }
            3 => {
                if v_isShared_10117_ == 0 {
                    v___x_10119_ = v___x_10116_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10120_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10120_, 0, v_a_10114_);
                    v___x_10119_ = v_reuseFailAlloc_10120_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_10119_;
            }
            5 => {
                if v_isShared_10125_ == 0 {
                    v___x_10127_ = v___x_10124_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_10128_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10128_, 0, v_a_10122_);
                    v___x_10127_ = v_reuseFailAlloc_10128_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_10127_;
            }
            7 => {
                if v_isShared_10133_ == 0 {
                    v___x_10135_ = v___x_10132_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_10136_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_10136_, 0, v_a_10130_);
                    v___x_10135_ = v_reuseFailAlloc_10136_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_10135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed(
    mut v_mvarId_10138_: *mut leanh::LeanObject,
    mut v___x_10139_: *mut leanh::LeanObject,
    mut v_fvarId_10140_: *mut leanh::LeanObject,
    mut v_failIfUnchanged_10141_: *mut leanh::LeanObject,
    mut v___y_10142_: *mut leanh::LeanObject,
    mut v___y_10143_: *mut leanh::LeanObject,
    mut v___y_10144_: *mut leanh::LeanObject,
    mut v___y_10145_: *mut leanh::LeanObject,
    mut v___y_10146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_failIfUnchanged_boxed_10147_: u8 = 0;
    let mut v_res_10148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_failIfUnchanged_boxed_10147_ = (leanh::lean_unbox(v_failIfUnchanged_10141_) as u8);
    v_res_10148_ = l_Lean_MVarId_letToHaveLocalDecl___lam__0(
        v_mvarId_10138_,
        v___x_10139_,
        v_fvarId_10140_,
        v_failIfUnchanged_boxed_10147_,
        v___y_10142_,
        v___y_10143_,
        v___y_10144_,
        v___y_10145_,
    );
    leanh::lean_dec(v___y_10145_);
    leanh::lean_dec_ref(v___y_10144_);
    leanh::lean_dec(v___y_10143_);
    leanh::lean_dec_ref(v___y_10142_);
    return v_res_10148_;
}
pub unsafe fn l_Lean_MVarId_letToHaveLocalDecl(
    mut v_mvarId_10149_: *mut leanh::LeanObject,
    mut v_fvarId_10150_: *mut leanh::LeanObject,
    mut v_failIfUnchanged_10151_: u8,
    mut v_a_10152_: *mut leanh::LeanObject,
    mut v_a_10153_: *mut leanh::LeanObject,
    mut v_a_10154_: *mut leanh::LeanObject,
    mut v_a_10155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_10159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10157_ = l_Lean_MVarId_letToHave___closed__1;
    v___x_10158_ = leanh::lean_box((v_failIfUnchanged_10151_) as usize);
    leanh::lean_inc(v_mvarId_10149_);
    v___f_10159_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_letToHaveLocalDecl___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___f_10159_, 0, v_mvarId_10149_);
    leanh::lean_closure_set(v___f_10159_, 1, v___x_10157_);
    leanh::lean_closure_set(v___f_10159_, 2, v_fvarId_10150_);
    leanh::lean_closure_set(v___f_10159_, 3, v___x_10158_);
    v___x_10160_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_extractLets_spec__3___redArg(
        v_mvarId_10149_,
        v___f_10159_,
        v_a_10152_,
        v_a_10153_,
        v_a_10154_,
        v_a_10155_,
    );
    return v___x_10160_;
}
pub unsafe fn l_Lean_MVarId_letToHaveLocalDecl___boxed(
    mut v_mvarId_10161_: *mut leanh::LeanObject,
    mut v_fvarId_10162_: *mut leanh::LeanObject,
    mut v_failIfUnchanged_10163_: *mut leanh::LeanObject,
    mut v_a_10164_: *mut leanh::LeanObject,
    mut v_a_10165_: *mut leanh::LeanObject,
    mut v_a_10166_: *mut leanh::LeanObject,
    mut v_a_10167_: *mut leanh::LeanObject,
    mut v_a_10168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_failIfUnchanged_boxed_10169_: u8 = 0;
    let mut v_res_10170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_failIfUnchanged_boxed_10169_ = (leanh::lean_unbox(v_failIfUnchanged_10163_) as u8);
    v_res_10170_ = l_Lean_MVarId_letToHaveLocalDecl(
        v_mvarId_10161_,
        v_fvarId_10162_,
        v_failIfUnchanged_boxed_10169_,
        v_a_10164_,
        v_a_10165_,
        v_a_10166_,
        v_a_10167_,
    );
    leanh::lean_dec(v_a_10167_);
    leanh::lean_dec_ref(v_a_10166_);
    leanh::lean_dec(v_a_10165_);
    leanh::lean_dec_ref(v_a_10164_);
    return v_res_10170_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Lets(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_LetToHave(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_ExtractLets_instInhabitedState_default =
        _init_l_Lean_Meta_ExtractLets_instInhabitedState_default();
    leanh::lean_mark_persistent(l_Lean_Meta_ExtractLets_instInhabitedState_default);
    l_Lean_Meta_ExtractLets_instInhabitedState = _init_l_Lean_Meta_ExtractLets_instInhabitedState();
    leanh::lean_mark_persistent(l_Lean_Meta_ExtractLets_instInhabitedState);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Lets(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Lets(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Replace(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_LetToHave(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Lets(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Lets(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Lets(builtin);
}